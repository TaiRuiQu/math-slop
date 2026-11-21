module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Exact counts of CRT classes surviving the second coprimality filter. -/

open Finset
open scoped BigOperators

namespace PrescribedSWidth

@[expose] public section

noncomputable section

def allowedResidues (R : ℕ) [NeZero R] (t : ZMod R) : Finset (ZMod R) := by
  classical
  exact univ.filter fun r => IsUnit r ∧ IsUnit (r + t)

theorem mem_allowedResidues {R : ℕ} [NeZero R] (r t : ZMod R) :
    r ∈ allowedResidues R t ↔ IsUnit r ∧ IsUnit (r + t) := by
  classical
  simp [allowedResidues]

theorem allowedResidues_card_prime {p : ℕ} [Fact p.Prime] (t : ZMod p) :
    (allowedResidues p t).card = if t = 0 then p - 1 else p - 2 := by
  classical
  have hset : allowedResidues p t = ((univ : Finset (ZMod p)).erase 0).erase (-t) := by
    ext r
    rw [mem_allowedResidues, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
    simp [← eq_neg_iff_add_eq_zero, and_comm]
  rw [hset]
  by_cases ht : t = 0
  · simp [ht, Finset.card_erase_of_mem, ZMod.card]
  · have hmem : -t ∈ (univ : Finset (ZMod p)).erase 0 := by simp [ht]
    rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (mem_univ _), card_univ,
      ZMod.card, ite_eq_right ht]
    omega

theorem allowedResidues_card_mul {R₁ R₂ : ℕ} [NeZero R₁] [NeZero R₂] [NeZero (R₁ * R₂)]
    (h : R₁.Coprime R₂) (t : ZMod (R₁ * R₂)) :
    (allowedResidues (R₁ * R₂) t).card =
      (allowedResidues R₁ ((ZMod.chineseRemainder h t).1)).card *
      (allowedResidues R₂ ((ZMod.chineseRemainder h t).2)).card := by
  classical
  let e := ZMod.chineseRemainder h
  have hmap : (allowedResidues (R₁ * R₂) t).map e.toEquiv.toEmbedding =
      (allowedResidues R₁ ((e t).1)) ×ˢ (allowedResidues R₂ ((e t).2)) := by
    ext r
    rw [mem_map_equiv, mem_allowedResidues, mem_product, mem_allowedResidues,
      mem_allowedResidues, ← isUnit_map_iff e, ← isUnit_map_iff e, map_add]
    change (IsUnit (e (e.symm r)) ∧ IsUnit (e (e.symm r) + e t)) ↔
      (IsUnit r.1 ∧ IsUnit (r.1 + (e t).1)) ∧ (IsUnit r.2 ∧ IsUnit (r.2 + (e t).2))
    simp only [e.apply_symm_apply, Prod.isUnit_iff, Prod.fst_add, Prod.snd_add]
    tauto
  simpa [e, card_product] using congrArg Finset.card hmap

theorem allowedResidues_card_prime_natCast {p : ℕ} [Fact p.Prime] (m : ℕ) :
    (allowedResidues p (m : ZMod p)).card = if p ∣ m then p - 1 else p - 2 := by
  simp only [allowedResidues_card_prime, ZMod.natCast_eq_zero_iff]

theorem allowedResidues_card_neg {R : ℕ} [NeZero R] (t : ZMod R) :
    (allowedResidues R (-t)).card = (allowedResidues R t).card := by
  classical
  let e : ZMod R ≃ ZMod R := Equiv.neg _
  have hmap : (allowedResidues R (-t)).map e.toEmbedding = allowedResidues R t := by
    ext r
    rw [mem_map_equiv, mem_allowedResidues, mem_allowedResidues]
    change (IsUnit (-r) ∧ IsUnit (-r + -t)) ↔ IsUnit r ∧ IsUnit (r + t)
    rw [← neg_add, IsUnit.neg_iff, IsUnit.neg_iff]
  simpa using congrArg Finset.card hmap

def allowedResidueCount (R m : ℕ) : ℕ :=
  if h : R = 0 then 0
  else
    have : NeZero R := ⟨h⟩
    (allowedResidues R (m : ZMod R)).card

theorem allowedResidueCount_eq (R : ℕ) [NeZero R] (m : ℕ) :
    allowedResidueCount R m = (allowedResidues R (m : ZMod R)).card := by
  simp [allowedResidueCount, NeZero.ne R]

/-- The factor `ν(m)` for a product of distinct primes. -/
theorem allowedResidueCount_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    allowedResidueCount (∏ p ∈ P, p) m =
      ∏ p ∈ P, (if p ∣ m then p - 1 else p - 2) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [prod_empty, allowedResidueCount_eq]
    have hset : allowedResidues 1 (m : ZMod 1) = univ := by
      ext r
      simp only [mem_allowedResidues, mem_univ, iff_true]
      constructor <;> exact isUnit_of_subsingleton _
    rw [hset, card_univ, ZMod.card]
  | @insert p P hp ih =>
    simp only [prod_insert hp]
    have hprime := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have : Fact p.Prime := ⟨hprime⟩
    have hpP : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (hprime.coprime_iff_not_dvd).2
        (fun h => hp ((Nat.prime_dvd_prime_iff_eq hprime (hP' q hq)).1 h ▸ hq))
    have : NeZero (∏ q ∈ P, q) :=
      ⟨prod_ne_zero_iff.2 (fun q hq => (hP' q hq).ne_zero)⟩
    rw [allowedResidueCount_eq, allowedResidues_card_mul hpP]
    rw [map_natCast]
    change (allowedResidues p (m : ZMod p)).card *
        (allowedResidues (∏ q ∈ P, q) (m : ZMod (∏ q ∈ P, q))).card = _
    rw [allowedResidues_card_prime_natCast, ← allowedResidueCount_eq, ih hP']

end

end

end PrescribedSWidth
