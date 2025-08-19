variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun h => ⟨fun x => (h x).left, fun x => (h x).right⟩)
  (fun ⟨hp, hq⟩ x => ⟨hp x, hq x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h hp x => h x (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h => Or.elim h
  (fun hp x => Or.inl (hp x))
  (fun hq x => Or.inr (hq x))

variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun x => ⟨fun h => h x, fun hr _ => hr⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h => Classical.byCases
    (fun hr : r => Or.inr hr)
    (fun hnr => Or.inl (fun x => Or.elim (h x)
      (fun hp => hp)
      (fun hr => False.elim (hnr hr)))))
  (fun h => Or.elim h
    (fun hp x => Or.inl (hp x))
    (fun hr _ => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (fun h hr x => h x hr)
  (fun h x hr => h hr x)

section

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h1 := h barber
  have : ¬ (shaves barber barber) :=
    fun hb => (h1.mp hb) hb
  this (h1.mpr this)

end

section

def even (n : Nat) : Prop :=
  ∃ k, k + k = n

def prime (n : Nat) : Prop :=
  ∀ k, k ∣ n → k = 1 ∨ k = n

def infinitely_many_primes : Prop :=
  ∀ n, ∃ p, prime p ∧ p > n

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ k, 2 ^ (2 ^ k) + 1 = n

def infinitely_many_Fermat_primes : Prop :=
  ∀ n, ∃ p, Fermat_prime p ∧ p > n

def goldbach_conjecture : Prop :=
  ∀ n, even n → n > 2 → ∃ p q, prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop :=
  ∀ n, ¬ even n -> n > 5 → ∃ p q r, prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop :=
  ∀ n > 2, ¬ ∃ a b c, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ n + b ^ n = c ^ n

end

open Classical

example : (∃ x : α, r) → r :=
  fun h => Exists.elim h fun x hr => hr

example (a : α) : r → (∃ x : α, r) :=
  fun hr => Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun ⟨x, hp, hr⟩ => ⟨⟨x, hp⟩, hr⟩)
  (fun ⟨⟨x, hp⟩, hr⟩ => ⟨x, hp, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun ⟨x, h⟩ => Or.elim h
    (fun hp => Or.inl ⟨x, hp⟩)
    (fun hq => Or.inr ⟨x, hq⟩))
  (fun h => Or.elim h
    (fun ⟨x, hp⟩ => ⟨x, Or.inl hp⟩)
    (fun ⟨x, hq⟩ => ⟨x, Or.inr hq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h ⟨x, hx⟩ => hx (h x))
  (fun h x => byContradiction
    (fun hnp => h ⟨x, hnp⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun ⟨x, hp⟩ h => h x hp)
  (fun h => byContradiction
    (fun hnex =>
      have : ∀ x, ¬p x :=
        fun x => byContradiction
        (fun hp => hnex ⟨x, not_not.mp hp⟩)
      h this))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h x => byContradiction
  (fun hp => h ⟨x, not_not.mp hp⟩))
  (fun h ⟨x, hp⟩ => (h x) hp)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h => byContradiction
  (fun hnex =>
    have : ∀ x, p x :=
      fun x => byContradiction
      (fun hnp => False.elim (hnex ⟨x, hnp⟩))
    h this))
  (fun ⟨x, hnp⟩ h => hnp (h x))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun h ⟨x, hp⟩ => h x hp)
  (fun h x hp => h ⟨x, hp⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
  (fun ⟨x, hpr⟩ h => hpr (h x))
  (fun h => byContradiction
  (fun hnex => byCases
  (fun hall : ∀ x, p x => hnex ⟨a, fun _ => h hall⟩)
  (fun _ => have hr : r := h (fun x => byContradiction
    (fun hnp => hnex ⟨x, fun hp => False.elim (hnp hp)⟩))
  hnex ⟨a, fun _ => hr⟩)))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun ⟨x, hrp⟩ hr => ⟨x, hrp hr⟩)
  (fun h => byCases
  (fun hr : r => let ⟨x, hp⟩ := h hr
    ⟨x, fun _ => hp⟩)
  (fun hnr => ⟨a, fun hr => False.elim (hnr hr)⟩))
