/-
# Jet bounds for the periodisation of a function supported in a small ball

`Work.Diff.STE.B3.perR_jet_bound`: if `f : (Fin n → ℝ) → ℝ` is smooth, is supported in the ball of
radius `R ≤ 1/2`, and has all its derivatives of order `≤ N` bounded by `B`, then the periodisation

`z ↦ ∑' m : Fin n → ℤ, f (z + m)`

has its derivatives of order `≤ N` bounded by `2 ^ n * B`.

The point is that, at every point, **at most one** translate `f (· + m)` is non-zero, and near a
given point `z` only the `2 ^ n` lattice points of `perRbox z` can contribute.  Hence the
periodisation is, locally around `z`, a finite sum of `2 ^ n` translates of `f`, and the derivative
of a translate is the translate of the derivative.

The one genuinely geometric input is the localisation of the box (`perRbox z`), proved here as the
private lemma `perR_tsum_local`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.perR_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **Localisation of the lattice translates.**  If `f` is supported in the ball of radius `R ≤ 1/2`
and `z'` lies within `1/2` of `z`, then only the lattice points of the finite box `perRbox z` can
contribute to the periodisation `z' ↦ ∑' m : Fin n → ℤ, f (z' + m)` of `f` at `z'`. -/
private lemma perR_tsum_local {n : ℕ} {R : ℝ} (hR : R ≤ 1/2) {f : (Fin n → ℝ) → ℝ}
    (hsupp : Function.support f ⊆ Metric.ball 0 R) {z z' : Fin n → ℝ}
    (hz' : z' ∈ Metric.ball z (1/2)) {m : Fin n → ℤ} (hm : m ∉ perRbox z) :
    f (z' + perRlattice m) = 0 := by
  by_contra hne
  have hmem : z' + perRlattice m ∈ Function.support f := hne
  have hlt : ‖z' + perRlattice m‖ < R := by
    have h := hsupp hmem
    simpa [Metric.mem_ball, dist_eq_norm] using h
  have hz'l : ‖z' - z‖ < 1/2 := by
    have h := hz'
    simpa [Metric.mem_ball, dist_eq_norm] using h
  refine hm ?_
  rw [perRbox_mem]
  intro i
  have h1' : |z' i + (m i : ℝ)| < R := by
    have h := norm_le_pi_norm (z' + perRlattice m) i
    rw [Real.norm_eq_abs] at h
    have := lt_of_le_of_lt h hlt
    simpa [perRlattice] using this
  have h2' : |z' i - z i| < 1/2 := by
    have h := norm_le_pi_norm (z' - z) i
    rw [Real.norm_eq_abs] at h
    have := lt_of_le_of_lt h hz'l
    simpa using this
  have hA : |z i - z' i| < 1/2 := by rw [abs_sub_comm]; exact h2'
  have h3 : |z i + (m i : ℝ)| < 1 := by
    have heq : z i + (m i : ℝ) = (z i - z' i) + (z' i + (m i : ℝ)) := by ring
    rw [heq]
    calc |(z i - z' i) + (z' i + (m i : ℝ))|
        ≤ |z i - z' i| + |z' i + (m i : ℝ)| := abs_add_le _ _
      _ < R + 1/2 := by linarith [add_lt_add hA h1']
      _ ≤ 1 := by linarith
  have hlo : ((-Int.floor (z i) - 2 : ℤ) : ℝ) < (m i : ℝ) := by
    have h := (abs_lt.mp h3).1
    have hf := Int.lt_floor_add_one (z i)
    push_cast
    linarith
  have hhi : (m i : ℝ) < ((-Int.floor (z i) + 1 : ℤ) : ℝ) := by
    have h := (abs_lt.mp h3).2
    have hf := Int.floor_le (z i)
    push_cast
    linarith
  constructor
  · have hh : (-Int.floor (z i) - 2 : ℤ) < m i := by exact_mod_cast hlo
    omega
  · have hh : m i < (-Int.floor (z i) + 1 : ℤ) := by exact_mod_cast hhi
    omega

/-- **The periodisation is a finite sum of `2 ^ n` translates near every point**, with the jet bound
carried over from `f`.  This is `perR_jet_bound` with the explicit constant `C = 2 ^ n`. -/
private lemma perR_jet_bound_aux {n N : ℕ} {R B : ℝ} (hR : R ≤ 1/2) (_hB : 0 ≤ B)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Metric.ball 0 R)
    (hbound : ∀ j, j ≤ N → ∀ w, ‖iteratedFDeriv ℝ j f w‖ ≤ B)
    {j : ℕ} (hj : j ≤ N) (z : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (fun z => ∑' m : Fin n → ℤ, f (z + perRlattice m)) z‖
      ≤ (2:ℝ)^n * B := by
  have hloc : ∀ z' ∈ Metric.ball z (1/2), ∀ m ∉ perRbox z, f (z' + perRlattice m) = 0 :=
    fun z' hz' m hm => perR_tsum_local hR hsupp hz' hm
  -- near `z`, the periodisation is the finite sum over the box
  have hEq : (fun z' => ∑' m : Fin n → ℤ, f (z' + perRlattice m))
      =ᶠ[nhds z] (fun z' => ∑ m ∈ perRbox z, f (z' + perRlattice m)) := by
    filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0:ℝ) < 1/2)] with z' hz'
    exact tsum_eq_sum (s := perRbox z) (fun m hm => hloc z' hz' m hm)
  have hsum : ∀ m ∈ perRbox z,
      ContDiffAt ℝ (j : ℕ∞) (fun z' : Fin n → ℝ => f (z' + perRlattice m)) z := by
    intro m _
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z' : Fin n → ℝ => f (z' + perRlattice m)) :=
      hf.comp (contDiff_id.add contDiff_const)
    exact (h1.of_le (by simp)).contDiffAt
  -- the derivative of the finite sum is the sum of the derivatives of the translates
  have hderiv : iteratedFDeriv ℝ j (fun z' => ∑' m : Fin n → ℤ, f (z' + perRlattice m)) z
      = ∑ m ∈ perRbox z, iteratedFDeriv ℝ j f (z + perRlattice m) := by
    rw [(hEq.iteratedFDeriv ℝ j).eq_of_nhds]
    rw [iteratedFDeriv_fun_sum_apply hsum]
    exact Finset.sum_congr rfl (fun m _ => iteratedFDeriv_comp_add_right j (perRlattice m) z)
  calc ‖iteratedFDeriv ℝ j (fun z' => ∑' m : Fin n → ℤ, f (z' + perRlattice m)) z‖
      = ‖∑ m ∈ perRbox z, iteratedFDeriv ℝ j f (z + perRlattice m)‖ := by rw [hderiv]
    _ ≤ ∑ m ∈ perRbox z, ‖iteratedFDeriv ℝ j f (z + perRlattice m)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ perRbox z, B := Finset.sum_le_sum (fun m _ => hbound j hj _)
    _ = (perRbox z).card • B := Finset.sum_const B
    _ = (2:ℝ)^n * B := by
        rw [perRbox_card, nsmul_eq_mul]
        push_cast
        ring

theorem perR_jet_bound (n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R B : ℝ), R ≤ 1 / 2 → 0 ≤ B →
      ∀ (f : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
      Function.support f ⊆ Metric.ball 0 R →
      (∀ (j : ℕ), j ≤ N → ∀ (w : Fin n → ℝ), ‖iteratedFDeriv ℝ j f w‖ ≤ B) →
      ∀ (j : ℕ), j ≤ N → ∀ (z : Fin n → ℝ),
        ‖iteratedFDeriv ℝ j
          (fun z : Fin n → ℝ => ∑' m : Fin n → ℤ, f (z + fun i => (m i : ℝ))) z‖ ≤ C * B := by
  refine ⟨(2:ℝ)^n, by positivity, ?_⟩
  intro R B hR hB f hf hsupp hbound j hj z
  exact perR_jet_bound_aux hR hB hf hsupp hbound hj z

end Work.Diff.STE.B3
