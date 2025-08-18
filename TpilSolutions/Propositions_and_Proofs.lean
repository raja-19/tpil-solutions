variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (fun h => And.intro (And.right h) (And.left h))
  (fun h => And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
   (fun h => Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq))
   (fun h => Or.elim h (fun hq => Or.inr hq) (fun hq => Or.inl hq))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
  (fun h => And.intro (h.left.left) (And.intro (h.left.right) (h.right)))
  (fun h => And.intro (And.intro h.left h.right.left) h.right.right)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (fun h => Or.elim h
    (fun hpq => Or.elim hpq
      (fun hp => Or.inl hp)
      (fun hq => Or.inr (Or.inl hq)))
    (fun hr => Or.inr (Or.inr hr)))
  (fun h => Or.elim h
    (fun hp => Or.inl (Or.inl hp))
    (fun hqr => Or.elim hqr
      (fun hq => Or.inl (Or.inr hq))
      (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (fun h => Or.elim h.right
  (fun hq => Or.inl ⟨h.left, hq⟩)
  (fun hr => Or.inr ⟨h.left, hr⟩))
  (fun h => Or.elim h
  (fun hpq => ⟨hpq.left, Or.inl hpq.right⟩)
  (fun hpr => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun h => Or.elim h
  (fun hp => ⟨Or.inl hp, Or.inl hp⟩)
  (fun ⟨hq, hr⟩ => ⟨Or.inr hq, Or.inr hr⟩))
  (fun ⟨hpq, hpr⟩ => Or.elim hpq
    (fun hp => Or.inl hp)
    (fun hq => Or.elim hpr
    (fun hp => Or.inl hp)
    (fun hr => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
  (fun h ⟨hp, hq⟩ => h hp hq)
  (fun h hp hq => h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
  (fun ⟨hpr, hqr⟩ hpq => Or.elim hpq
  (fun hp => hpr hp)
  (fun hq => hqr hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (fun h => ⟨fun hp => h (Or.inl hp) , fun hq => h (Or.inr hq)⟩)
  (fun ⟨hnp, hnq⟩ hpq => Or.elim hpq
  (fun hp => hnp hp)
  (fun hq => hnq hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h ⟨hp, hq⟩ => Or.elim h
  (fun hnp => hnp hp)
  (fun hnq => hnq hq)

example : ¬(p ∧ ¬p) :=
  fun ⟨hp, hnp⟩ => hnp hp

example : p ∧ ¬q → ¬(p → q) :=
  fun ⟨hp, hnq⟩ hpq => hnq (hpq hp)

example : ¬p → (p → q) :=
  fun hnp hp => False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  fun h hp => Or.elim h
  (fun hnp => False.elim (hnp hp))
  (fun hq => hq)

example : p ∨ False ↔ p :=
  Iff.intro
  (fun h => Or.elim h (fun hp => hp) (fun hfalse => False.elim hfalse))
  (fun hp => Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
  (fun ⟨_, hfalse⟩ => hfalse)
  (fun hfalse => False.elim hfalse)

example : (p → q) → (¬q → ¬p) :=
  fun hpq hnq hp => hnq (hpq hp)

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h => byCases
  (fun hq : q => Or.inl (fun _ => hq))
  (fun hnq => Or.inr (fun hp => Or.elim (h hp)
    (fun hq => False.elim (hnq hq))
    (fun hr => hr)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h => byCases
  (fun hp : p => Or.inr (fun hq => h ⟨hp, hq⟩))
  (fun hnp => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h => byCases
  (fun hp : p => And.intro hp
    (fun hq => False.elim (h fun _ => hq)))
  (fun hnp => And.intro
    (False.elim (h fun hp => False.elim (hnp hp)))
    (fun _ => h fun hp => False.elim (hnp hp)))

example : (p → q) → (¬p ∨ q) :=
  fun h => byCases
  (fun hp : p => Or.inr (h hp))
  (fun hnp => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  fun h hp => byCases
  (fun hq : q => hq)
  (fun hnq => False.elim ((h hnq) hp))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  fun h => byCases
  (fun hp : p => hp)
  (fun hnp =>
    have : p → q := fun hp => False.elim (hnp hp)
    h this)

example : ¬(p ↔ ¬p) :=
  fun h =>
    have hnp : ¬p := fun hp => (h.mp hp) hp
    hnp (h.mpr hnp)
