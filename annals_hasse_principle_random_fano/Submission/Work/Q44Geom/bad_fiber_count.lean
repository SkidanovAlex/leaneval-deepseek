import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.zero_count
import Submission.Work.Q44Geom.formOf_eval
import Submission.Work.Q44Geom.BadFiberAux
import Submission.Work.Q44Geom.eq_of_coset_eq
import Submission.Work.Q44Geom.bad_fiber_arith
import Submission.Work.Q44Geom.exists_gen_of_lat
import Submission.Work.Q44Geom.coset_ball_lower
import Submission.Work.HP.MDBasic.finite_sets

/-!
# `Work.Q44Geom.bad_fiber_count`

For a fixed primitive rank-`2` lattice `N` and a nonzero quartic form `f = f44 c`, the number
of lattices `L ∈ Sset c s` which have no good pair and satisfy `L ⊓ latW (f44 c) = N` is
`≪ s₁² s₂²`, uniformly in `c`, `s` and `N`.

The argument is a "coset" or "fiber" count, one fibre of the map `L ↦ L ⊓ W`:

* every such `L` contains `N` with `L = N + ℤ z` for a generator `z` of `L/N`
  (`BF.gen_of_le`), and `class_rep` produces such a generator with `‖z‖ ≤ 4 s₂`, because
  `λ₃(L) ≤ s₂` on `Sset c s` and `λ₂(N) ≤ s₁`;
* the map `L ↦ (z_L + N)` is injective (two lattices generated over `N` by congruent vectors
  coincide, `eq_of_coset_eq`), and the whole coset `z_L + N` lies in `L`, whence consists of
  zeros of `f` — a disjoint family of subsets of the ball of radius `8 s₂`;
* each coset contributes at least `c₀ (8 s₂)²/(λ₁(N)λ₂(N)) ≥ 64 c₀ s₂²/s₁²` lattice points
  of norm `≤ 8 s₂` (`coset_ball_lower`, from `vdc_lower`), while `f` has at most
  `C₀ (8 s₂)⁴` integer zeros in that ball (`zero_count`);
* `ncard_mul_le_of_disjoint` converts this into `#G · (64 c₀ s₂²/s₁²) ≤ C₀ (8 s₂)⁴`, and
  `bad_fiber_arith` finishes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Q44Geom

open MvPolynomial
open Classical

/-! ## The zero set of `f44 c` in a ball -/

/-- The integral zeros of `f44 c` of Euclidean norm at most `T`. -/
def bf_zeroSet (c : Work.HP.Mon 4 4 → ℤ) (T : ℝ) : Set (Fin 5 → ℤ) :=
  {x | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval (Work.Q44Geom.toRatLM x) (f44 c) = 0}

lemma bf_zerSet_finite (c : Work.HP.Mon 4 4 → ℤ) (T : ℝ) : (bf_zeroSet c T).Finite :=
  (Work.HP.MDBasic.finite_eNorm_le (ι := Fin 5) T).subset fun x hx => hx.1

/-! ## The fibre count -/

theorem bad_fiber_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : Work.HP.Mon 4 4 → ℤ), Work.HP.formOf 4 4 c ≠ 0 →
      (Work.HP.formOf 4 4 c).totalDegree ≤ 4 →
      ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      ∀ (N : Submodule ℤ (Fin 5 → ℤ)), Work.HP.IsPrimLat N → Work.HP.rk N = 2 →
      Work.HP.lam N 2 ≤ s 1 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | L ∈ Work.Q44Geom.Sset c s ∧
        ¬ Work.Q44Geom.goodPair c s L ∧ L ⊓ Work.Q44Geom.latW (Work.Q44Geom.f44 c) = N} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ C * (s 1) ^ 2 * (s 2) ^ 2 := by
  obtain ⟨C0, hC0pos, hC0⟩ := zero_count
  obtain ⟨cc, hccpos, hcc⟩ := coset_ball_lower
  refine ⟨64 * C0 / cc + 1, by positivity, ?_⟩
  intro c hcne hdeg s hs0 hs01 hs12 N hNprim hNrk hNlam
  classical
  have hs1 : (1 : ℝ) ≤ s 1 := le_trans hs0 hs01
  have hs2 : (1 : ℝ) ≤ s 2 := le_trans hs1 hs12
  have hs2nonneg : (0 : ℝ) ≤ s 2 := le_trans zero_le_one hs2
  set G : Set (Submodule ℤ (Fin 5 → ℤ)) :=
    {L | L ∈ Sset c s ∧ ¬ goodPair c s L ∧ L ⊓ latW (f44 c) = N} with hG
  -- a short generator of `L` over `N`, for every `L ∈ G`
  have hex : ∀ L ∈ G, ∃ z : Fin 5 → ℤ, z ∈ L ∧
      (∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ N, w = k • z + n) ∧
      1 ≤ Work.HP.eNorm z ∧ Work.HP.eNorm z ≤ 4 * s 2 := by
    intro L hL
    rw [hG] at hL
    obtain ⟨hLS, -, hinf⟩ := hL
    have hNL : N ≤ L := by rw [← hinf]; exact inf_le_left
    exact exists_gen_of_lat hNprim hNrk hNlam hs12 hNL hLS
  let zOf : (L : Submodule ℤ (Fin 5 → ℤ)) → L ∈ G → (Fin 5 → ℤ) :=
    fun L hL => Classical.choose (hex L hL)
  have zOf_spec : ∀ (L : Submodule ℤ (Fin 5 → ℤ)) (hL : L ∈ G), zOf L hL ∈ L ∧
      (∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ N, w = k • zOf L hL + n) ∧
      1 ≤ Work.HP.eNorm (zOf L hL) ∧ Work.HP.eNorm (zOf L hL) ≤ 4 * s 2 :=
    fun L hL => Classical.choose_spec (hex L hL)
  -- the contribution of each lattice: the points of the coset `z + N` in the ball of radius `8 s₂`
  let t : Submodule ℤ (Fin 5 → ℤ) → Set (Fin 5 → ℤ) := fun L =>
    if h : L ∈ G then {v : Fin 5 → ℤ | v - zOf L h ∈ N ∧ Work.HP.eNorm v ≤ 8 * s 2} else ∅
  have ht : ∀ (L : Submodule ℤ (Fin 5 → ℤ)) (hL : L ∈ G),
      t L = {v : Fin 5 → ℤ | v - zOf L hL ∈ N ∧ Work.HP.eNorm v ≤ 8 * s 2} :=
    fun L hL => dif_pos hL
  -- each member contributes at least one point
  have hne : ∀ L ∈ G, (t L).Nonempty := by
    intro L hL
    rw [ht L hL]
    obtain ⟨hzL, -, hz1, hzn⟩ := zOf_spec L hL
    refine ⟨zOf L hL, ?_, ?_⟩
    · rw [sub_self]; exact N.zero_mem
    · linarith
  -- and all of them lie in the zero set of `f`
  have hsub : ∀ L ∈ G, t L ⊆ bf_zeroSet c (8 * s 2) := by
    intro L hL v hv
    rw [ht L hL] at hv
    obtain ⟨hvN, hvR⟩ := hv
    have hLg := hL
    rw [hG] at hLg
    obtain ⟨hLS, -, hinf⟩ := hLg
    have hNL : N ≤ L := by rw [← hinf]; exact inf_le_left
    obtain ⟨hzL, -, -, -⟩ := zOf_spec L hL
    have hvL : v ∈ L := by
      have h1 : (v - zOf L hL) + zOf L hL ∈ L := Submodule.add_mem L (hNL hvN) hzL
      rwa [sub_add_cancel] at h1
    refine ⟨hvR, ?_⟩
    have hvanish := (Work.HP.mem_vanishOn (L := L) (a := c)).mp hLS.2.2.2 ⟨v, hvL⟩
    rw [formOf_eval c v, hvanish, Int.cast_zero]
  -- distinct lattices give disjoint cosets
  have hdisj : ∀ L ∈ G, ∀ L' ∈ G, L ≠ L' → Disjoint (t L) (t L') := by
    intro L hL L' hL' hne'
    rw [Set.disjoint_left]
    intro v hv hv'
    rw [ht L hL] at hv
    rw [ht L' hL'] at hv'
    obtain ⟨hvN, -⟩ := hv
    obtain ⟨hvN', -⟩ := hv'
    have hzy : zOf L hL - zOf L' hL' ∈ N := by
      have h1 : (v - zOf L' hL') - (v - zOf L hL) ∈ N := N.sub_mem hvN' hvN
      have h2 : (v - zOf L' hL') - (v - zOf L hL) = zOf L hL - zOf L' hL' := by abel
      rwa [h2] at h1
    have hLg := hL
    have hLg' := hL'
    rw [hG] at hLg hLg'
    obtain ⟨-, -, hinf⟩ := hLg
    obtain ⟨-, -, hinf'⟩ := hLg'
    have hNL : N ≤ L := by rw [← hinf]; exact inf_le_left
    have hNL' : N ≤ L' := by rw [← hinf']; exact inf_le_left
    exact hne' (eq_of_coset_eq hNL hNL' (zOf_spec L hL).2.1 (zOf_spec L' hL').2.1
      (zOf_spec L hL).1 (zOf_spec L' hL').1 hzy)
  -- each coset contributes `≫ s₂²/s₁²` points
  have hk : ∀ L ∈ G, 64 * cc * ((s 2) ^ 2 / (s 1) ^ 2) ≤ ((t L).ncard : ℝ) := by
    intro L hL
    rw [ht L hL]
    obtain ⟨hzL, -, hz1, hzn⟩ := zOf_spec L hL
    have hmain := hcc N hNrk (zOf L hL) (8 * s 2) hz1 (by linarith)
    -- `λ₁(N) λ₂(N) ≤ s₁²`
    have hlam1 : Work.HP.lam N 1 ≤ Work.HP.lam N 2 :=
      Work.HP.lam_mono N (by norm_num) (by omega)
    have hp1 : (0 : ℝ) < Work.HP.lam N 1 := Work.HP.lam_pos N (by norm_num) (by omega)
    have hp2 : (0 : ℝ) < Work.HP.lam N 2 := Work.HP.lam_pos N (by norm_num) (by omega)
    have hs1pos : (0 : ℝ) < s 1 := lt_of_lt_of_le zero_lt_one hs1
    have hprod : Work.HP.lam N 1 * Work.HP.lam N 2 ≤ (s 1) ^ 2 := by
      have h := mul_le_mul (le_trans hlam1 hNlam) hNlam (le_of_lt hp2) (le_of_lt hs1pos)
      rwa [pow_two]
    have hprodpos : (0 : ℝ) < Work.HP.lam N 1 * Work.HP.lam N 2 := mul_pos hp1 hp2
    have hsq1pos : (0 : ℝ) < (s 1) ^ 2 := by positivity
    have hle_div : (8 * s 2) ^ 2 / (s 1) ^ 2
        ≤ (8 * s 2) ^ 2 / (Work.HP.lam N 1 * Work.HP.lam N 2) := by
      exact div_le_div_of_nonneg_left (by positivity) hprodpos hprod
    refine le_trans ?_ hmain
    calc 64 * cc * ((s 2) ^ 2 / (s 1) ^ 2)
        = cc * ((8 * s 2) ^ 2 / (s 1) ^ 2) := by ring
      _ ≤ cc * ((8 * s 2) ^ 2 / (Work.HP.lam N 1 * Work.HP.lam N 2)) :=
          mul_le_mul_of_nonneg_left hle_div (le_of_lt hccpos)
  -- assemble
  have hcount := BF.ncard_mul_le_of_disjoint G t (bf_zeroSet c (8 * s 2))
    (64 * cc * ((s 2) ^ 2 / (s 1) ^ 2)) (bf_zerSet_finite c (8 * s 2)) hne hsub hdisj hk
  have hZ : ((bf_zeroSet c (8 * s 2)).ncard : ℝ) ≤ C0 * (8 * s 2) ^ 4 :=
    hC0 (f44 c) hcne hdeg (8 * s 2) (by linarith)
  show (G.ncard : ℝ) ≤ (64 * C0 / cc + 1) * (s 1) ^ 2 * (s 2) ^ 2
  exact bad_fiber_arith hC0pos hccpos hs1 hs12 hcount hZ

end Work.Q44Geom
