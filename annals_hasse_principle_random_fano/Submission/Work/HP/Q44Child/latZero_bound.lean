import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Q44Child.latZeroGeom
import Submission.Work.HP.Q44Child.latZeroCount

/-!
# `N_c(Z;L) ≪ (Z/λ₁)(Z/λ₂)` for quartic threefolds

`Work.HP.Q44Child.latZero_bound`: for a rank-`3` sublattice `L ⊆ ℤ^5` and a quartic form `a` that
does not vanish identically on `L`, the number of lattice points of `L` of Euclidean norm at most
`Z` at which `a` vanishes is `≪ (1 + Z/λ₁(L))(1 + Z/λ₂(L))`.

This is the bound `N_c(Z;L) ≪ (Z/s₁)(Z/s₂)` of Browning–Le Boudec–Sawin §3.4 in the
non-degenerate case (their set `T_{3,4}`).  The proof combines two inputs:

* `Work.HP.Q44Child.exists_geomTriple` / `geomTriple_bounds` (file `latZeroGeom.lean`): a
  *reduced basis* `b₀,b₁,b₂` of `L` (Davenport's construction), with `b₀` of minimal norm and the
  coefficient bounds `t₁²λ₂² ≤ 16‖x‖²`, `t₂²λ₃² ≤ 16‖x‖²` for `x = t₀b₀+t₁b₁+t₂b₂`;
* `Work.HP.Q44Child.latZeroCount` (file `latZeroCount.lean`): the fibre count over `(t₁,t₂)`,
  using that for fixed `(t₁,t₂)` the restriction of `a` is a univariate polynomial in `t₀` of
  degree `≤ 4`, together with Schwartz–Zippel for the exceptional fibres.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.HP.Q44Child

open Work.HP

theorem latZero_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (Fin 5 → ℤ)), Work.HP.rk L = 3 →
      ∀ (a : Work.HP.Mon 4 4 → ℤ), a ∉ Work.HP.vanishOn L → ∀ Z : ℝ, 1 ≤ Z →
      (({x : Fin 5 → ℤ | x ∈ L ∧ Work.HP.eNorm x ≤ Z ∧ Work.HP.formEval 4 4 a x = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ C * (1 + Z / Work.HP.lam L 1) * (1 + Z / Work.HP.lam L 2) := by
  refine ⟨2000000, by norm_num, ?_⟩
  intro L hL a ha Z hZ
  obtain ⟨b₀, b₁, b₂, htri⟩ := exists_geomTriple L hL
  let b : Fin 3 → (Fin 5 → ℤ) := ![b₀, b₁, b₂]
  have hb0 : b 0 = b₀ := rfl
  have hb1 : b 1 = b₁ := rfl
  have hb2 : b 2 = b₂ := rfl
  have hspan : Submodule.span ℤ (Set.range b) = L := by
    have hrange : Set.range b = ({b₀, b₁, b₂} : Set (Fin 5 → ℤ)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [b]
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    rw [hrange]; exact htri.span_eq
  have hbmin : ∀ y ∈ L, y ≠ 0 → Work.HP.eNorm (b 0) ≤ Work.HP.eNorm y := by
    intro y hy hy0
    rw [hb0]; exact htri.min₀ y hy hy0
  have h1 : Work.HP.lam L 1 ≤ Work.HP.lam L 2 :=
    Work.HP.lam_mono L (by norm_num) (by omega)
  have h23 : Work.HP.lam L 2 ≤ Work.HP.lam L 3 :=
    Work.HP.lam_mono L (by norm_num) (by omega)
  have h2pos : 0 < Work.HP.lam L 2 := Work.HP.lam_pos L (by norm_num) (by omega)
  have h3pos : 0 < Work.HP.lam L 3 := Work.HP.lam_pos L (by norm_num) (by omega)
  have hne : ¬ (∀ u ∈ L, Work.HP.formEval 4 4 a u = 0) := by
    intro h
    refine ha ?_
    rw [mem_vanishOn]
    intro u
    exact h (u : Fin 5 → ℤ) u.2
  -- `eNorm b₀ = λ₁`
  have hb0eq : Work.HP.eNorm (b 0) = Work.HP.lam L 1 := by
    refine le_antisymm ?_ (Work.HP.lam_one_le_eNorm L htri.mem₀ htri.ne₀)
    rw [hb0]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨f, hfL, hfI, hfε⟩ :=
      Work.HP.lam_witness L (i := 1) (by omega) (ρ := Work.HP.lam L 1 + ε) (by linarith)
    exact (htri.min₀ (f 0) (hfL 0) (hfI.ne_zero 0)).trans (hfε 0)
  have hb0l2 : Work.HP.eNorm (b 0) ≤ Work.HP.lam L 2 := hb0eq.trans_le h1
  -- the coefficient bounds in the form required by the counting lemma
  have hkey : ∀ c : Fin 3 → ℤ,
      |(c 1 : ℝ)| * Work.HP.lam L 2 ≤ 16 * Work.HP.eNorm (∑ j, c j • b j) ∧
      |(c 2 : ℝ)| * Work.HP.lam L 3 ≤ 16 * Work.HP.eNorm (∑ j, c j • b j) := by
    intro c
    obtain ⟨h1', h2'⟩ := geomTriple_bounds L hL htri c
    constructor
    · have hx : (0:ℝ) ≤ Work.HP.eNorm (∑ j, c j • b j) := Work.HP.eNorm_nonneg _
      have hsq : ((c 1 : ℝ)) ^ 2 * Work.HP.lam L 2 ^ 2
          ≤ (16 * Work.HP.eNorm (∑ j, c j • b j)) ^ 2 := by
        calc ((c 1 : ℝ)) ^ 2 * Work.HP.lam L 2 ^ 2
            ≤ 16 * Work.HP.eNorm (∑ j, c j • b j) ^ 2 := h1'
          _ ≤ (16 * Work.HP.eNorm (∑ j, c j • b j)) ^ 2 := by nlinarith [hx]
      have h4 : (0:ℝ) ≤ 16 * Work.HP.eNorm (∑ j, c j • b j) := by positivity
      calc |(c 1 : ℝ)| * Work.HP.lam L 2
          = Real.sqrt (((c 1 : ℝ)) ^ 2 * Work.HP.lam L 2 ^ 2) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
              Real.sqrt_sq (le_of_lt h2pos)]
        _ ≤ Real.sqrt ((16 * Work.HP.eNorm (∑ j, c j • b j)) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 16 * Work.HP.eNorm (∑ j, c j • b j) := Real.sqrt_sq h4
    · have hx : (0:ℝ) ≤ Work.HP.eNorm (∑ j, c j • b j) := Work.HP.eNorm_nonneg _
      have hsq : ((c 2 : ℝ)) ^ 2 * Work.HP.lam L 3 ^ 2
          ≤ (16 * Work.HP.eNorm (∑ j, c j • b j)) ^ 2 := by
        calc ((c 2 : ℝ)) ^ 2 * Work.HP.lam L 3 ^ 2
            ≤ 16 * Work.HP.eNorm (∑ j, c j • b j) ^ 2 := h2'
          _ ≤ (16 * Work.HP.eNorm (∑ j, c j • b j)) ^ 2 := by nlinarith [hx]
      have h4 : (0:ℝ) ≤ 16 * Work.HP.eNorm (∑ j, c j • b j) := by positivity
      calc |(c 2 : ℝ)| * Work.HP.lam L 3
          = Real.sqrt (((c 2 : ℝ)) ^ 2 * Work.HP.lam L 3 ^ 2) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
              Real.sqrt_sq (le_of_lt h3pos)]
        _ ≤ Real.sqrt ((16 * Work.HP.eNorm (∑ j, c j • b j)) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 16 * Work.HP.eNorm (∑ j, c j • b j) := Real.sqrt_sq h4
  have hcount := latZeroCount b a L htri.linIndep hspan hbmin hne
    (Work.HP.lam L 2) (Work.HP.lam L 3) h2pos h3pos h23 hb0l2 hkey Z hZ
  refine hcount.trans ?_
  have hl1pos : 0 < Work.HP.lam L 1 := Work.HP.lam_pos L (by norm_num) (by omega)
  have hfac : 1 + Z / Work.HP.eNorm (b 0) ≤ (1 + Z / Work.HP.lam L 1) * 2 := by
    have hZ0 : (0:ℝ) ≤ Z := by linarith
    rw [hb0eq]
    nlinarith [div_nonneg hZ0 (le_of_lt hl1pos), hl1pos, hZ]
  calc 1000000 * (1 + Z / Work.HP.eNorm (b 0)) * (1 + Z / Work.HP.lam L 2)
      ≤ 1000000 * ((1 + Z / Work.HP.lam L 1) * 2) * (1 + Z / Work.HP.lam L 2) := by
        have h2 : (0:ℝ) ≤ 1 + Z / Work.HP.lam L 2 := by positivity
        nlinarith [hfac, h2]
    _ = 2000000 * (1 + Z / Work.HP.lam L 1) * (1 + Z / Work.HP.lam L 2) := by ring

end Work.HP.Q44Child
