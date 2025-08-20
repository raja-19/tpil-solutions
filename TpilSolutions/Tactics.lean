variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  repeat intro ⟨h1, h2⟩; exact ⟨h2, h1⟩

example : p ∨ q ↔ q ∨ p := by
  constructor
  repeat intro
  | Or.inl h => exact Or.inr h
  | Or.inr h => exact Or.inl h

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · intro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro
    | Or.inl hpq => cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | Or.inr hr => exact Or.inr (Or.inr hr)
  · intro
    | Or.inl hp => exact Or.inl (Or.inl hp)
    | Or.inr hqr => cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩
  · intro
    | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
    | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · intro
    | Or.inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
    | Or.inr ⟨hq, hr⟩ => exact ⟨Or.inr hq, Or.inr hr⟩
  · intro ⟨hpq, hqr⟩
    cases hpq with
    | inl hp => exact Or.inl hp
    | inr hq => cases hqr with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by simp

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro ⟨hpr, hqr⟩
    intro
    | Or.inl hp => exact hpr hp
    | Or.inr hq => exact hqr hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by simp

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | Or.inl hnp => intro hpq; exact hnp (hpq.left)
  | Or.inr hnq => intro hpq; exact hnq (hpq.right)

example : ¬(p ∧ ¬p) := by simp

example : p ∧ ¬q → ¬(p → q) := by simp

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro
  | Or.inl hnp => intro hp; contradiction
  | Or.inr hq => intro _; exact hq

example : p ∨ False ↔ p := by simp

example : p ∧ False ↔ False := by simp

example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
  exact hnq (h hp)

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases (em p) with
  | inl hp => cases (h hp) with
    | inl hq => simp [hp, hq]
    | inr hr => simp [hp, hr]
  | inr hnp => simp [hnp]

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (em p) with
  | inl hp =>
    apply Or.inr
    intro hq
    exact h ⟨hp, hq⟩
  | inr hnp =>
    apply Or.inl
    assumption

example : ¬(p → q) → p ∧ ¬q := by simp

example : (p → q) → (¬p ∨ q) := by
  intro h
  cases (em p) with
  | inl hp => simp [h, hp]
  | inr hnp => simp [hnp]

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  cases (em q) with
  | inl hq => exact hq
  | inr hnq =>
    have := h hnq
    contradiction

example : p ∨ ¬p := by
  apply em p

example : (((p → q) → p) → p) := by
  intro h
  cases (em p) with
  | inl hp => assumption
  | inr hnp =>
    have : p → q := by
      intro hp
      contradiction
    exact h this

example : ¬(p ↔ ¬p) := by simp

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor <;> (intro h; simp [h])

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h hp x
  exact h x (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro
  | Or.inl hp => simp [hp]
  | Or.inr hq => simp [hq]

variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro x
  constructor
  · intro h
    exact h x
  · intro hr x
    exact hr

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  · intro h
    cases (em r) with
    | inl hr => simp [hr]
    | inr hnr =>
      apply Or.inl
      intro x
      simp [hnr] at h
      exact h x
  · intro
    | Or.inl h => simp [h]
    | Or.inr hr => simp [hr]

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  · intro h hr
    simp [h, hr]
  · intro h x hr
    simp [h, hr]

section

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have h1 := h barber
  revert h1
  simp

end

open Classical

example : (∃ x : α, r) → r := by simp

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exists a

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by simp

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro ⟨x, hpq⟩
    cases hpq with
    | inl hp => exact Or.inl ⟨x, hp⟩
    | inr hq => exact Or.inr ⟨x, hq⟩
  · intro
    | Or.inl ⟨x, hp⟩ => exact ⟨x, Or.inl hp⟩
    | Or.inr ⟨x, hq⟩ => exact ⟨x, Or.inr hq⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by simp

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by simp

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by simp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by simp

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by simp

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  · intro ⟨x, hpr⟩ h
    exact hpr (h x)
  · intro h
    cases em (∀ x, p x) with
    | inl hall =>
      exists a
      simp [h hall]
    | inr hnall =>
      simp at hnall
      have ⟨x, hnp⟩ := hnall
      exact ⟨x, by simp [hnp]⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  · intro ⟨x, hrp⟩ hr
    exact ⟨x, hrp hr⟩
  · intro h
    cases (em r) with
    | inl hr =>
      have ⟨x, hp⟩ := h hr
      exact ⟨x, by simp [hp]⟩
    | inr hnr => exact ⟨a, by simp [hnr]⟩

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> constructor <;> (first | assumption | apply Or.inr) <;>
    first | apply Or.inl; assumption | apply Or.inr; assumption
