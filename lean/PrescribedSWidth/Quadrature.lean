module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! The rectangle estimate for a fixed smooth weight can be stated using its
Lipschitz constant. On the compact support it supplies a uniform lattice bound. -/

open MeasureTheory Set Finset
open scoped Interval

@[expose] public section

namespace PrescribedSWidth

private theorem meshCell {f : ℝ → ℝ} {D : NNReal} (hf : LipschitzWith D f)
    {a b : ℝ} (hab : a ≤ b) :
    |(b-a) * f b - ∫ x in a..b, f x| ≤ ((D : ℝ) * (b-a)) * (b-a) := by
  rw [← smul_eq_mul, ← intervalIntegral.integral_const,
    ← intervalIntegral.integral_sub (continuous_const.intervalIntegrable a b)
      (hf.continuous.intervalIntegrable a b),
    ← Real.norm_eq_abs]
  have hbd : ∀ x ∈ uIoc a b, ‖f b - f x‖ ≤ (D : ℝ) * (b-a) := by
    intro x hx
    rw [uIoc_of_le hab] at hx
    have hgeom : dist b x ≤ b-a := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hx.2)]
      linarith [hx.1]
    have h := hf.dist_le_mul_of_le hgeom
    simpa only [Real.dist_eq, Real.norm_eq_abs] using h
  simpa [abs_of_nonneg (sub_nonneg.2 hab), mul_comm, mul_left_comm, mul_assoc] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbd

/-- Summing the right-endpoint rectangle error over a uniform mesh. -/
theorem meshSum_error {f : ℝ → ℝ} {D : NNReal} (hf : LipschitzWith D f)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    |δ * (∑ j ∈ range n, f ((j+1 : ℝ) * δ)) - ∫ x in 0..(n*δ), f x| ≤
      n * ((D : ℝ) * δ^2) := by
  have hin (j : ℕ) (hj : j < n) :
      IntervalIntegrable f volume ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) :=
    hf.continuous.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hin
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at hsum
  rw [← hsum, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ range n, (D : ℝ) * δ^2 := by
      apply sum_le_sum
      intro j _
      have hseg : (j : ℝ)*δ ≤ (j+1 : ℝ)*δ := by nlinarith
      have h := meshCell hf hseg
      rw [show (j+1 : ℝ)*δ - j*δ = δ by ring] at h
      simpa only [sq, mul_assoc] using h
    _ = _ := by simp [nsmul_eq_mul]

/-- For a weight of integral zero over the mesh, the discretization error is
the whole sum. If the mesh endpoint is bounded, this bound is independent of
the mesh size. -/
theorem meshSum_le_of_zero_integral {f : ℝ → ℝ} {D : NNReal}
    (hf : LipschitzWith D f) {δ B : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : (n : ℝ)*δ ≤ B) (hzero : ∫ x in 0..(n*δ), f x = 0) :
    |∑ j ∈ range n, f ((j+1 : ℝ)*δ)| ≤ (D : ℝ)*B := by
  have hh := meshSum_error hf hδ n
  rw [hzero, sub_zero, abs_mul, abs_of_pos hδ, show
    (n : ℝ) * ((D : ℝ) * δ^2) = δ * ((D : ℝ) * ((n : ℝ) * δ)) by ring] at hh
  exact ((mul_le_mul_iff_of_pos_left hδ).1 hh).trans
    (mul_le_mul_of_nonneg_left hn D.coe_nonneg)

end PrescribedSWidth

end
