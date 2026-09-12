import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Order.CompletePartialOrder

open Metric
open scoped Topology

namespace Commons.Geometry.Convex.Hadwiger

/-- Strict separation of a point from a closed convex set in a (real) Hilbert space: if
`x ∉ P` and `P` is closed, convex and nonempty, then some nonzero vector `n` separates
strictly, i.e. `⟪n, y⟫ < ⟪n, x⟫` for every `y ∈ P`. -/
lemma strict_separate_point_of_not_mem {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    {P : Set V} (hPconv : Convex ℝ P) (hPcl : IsClosed P)
    {x : V} (hx : x ∉ P) (hPne : P.Nonempty) :
    ∃ n : V, n ≠ 0 ∧ ∀ y ∈ P, inner ℝ n y < inner ℝ n x := by
  classical
  rcases geometric_hahn_banach_closed_point (E := V) hPconv hPcl hx with ⟨f, u, hfA, hfx⟩
  rcases hPne with ⟨p, hpP⟩
  let n : V := (InnerProductSpace.toDual ℝ V).symm f
  have hn_ne : n ≠ 0 := by
    intro hn0
    have hf0 : f = 0 := by
      have h := congrArg (InnerProductSpace.toDual ℝ V) hn0
      simpa [n] using h
    have hfp : f p < u := hfA p hpP
    have hfxu : u < f x := hfx
    simp [hf0] at hfp hfxu
    linarith
  refine ⟨n, hn_ne, ?_⟩
  intro y hy
  have hy1 : inner ℝ n y = f y := by
    change inner ℝ ((InnerProductSpace.toDual ℝ V).symm f) y = f y
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := y) (y := f)
  have hx1 : inner ℝ n x = f x := by
    change inner ℝ ((InnerProductSpace.toDual ℝ V).symm f) x = f x
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := x) (y := f)
  rw [hy1, hx1]
  exact lt_trans (hfA y hy) hfx

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- If small steps of size at most `δ` in direction `v` leave the compact convex set `P`,
then `f₀` has a nonzero supporting functional whose value on `v` is nonnegative. -/
lemma exists_supporting_functional_vnonneg {P : Set V} (hPconv : Convex ℝ P)
    (hPcpt : IsCompact P) (v f₀ : V) (hf₀P : f₀ ∈ P)
    (δ : ℝ) (hδ : 0 < δ)
    (hray : ∀ ε : ℝ, 0 < ε → ε ≤ δ → f₀ + ε • v ∉ P) :
    ∃ n : V, n ≠ 0 ∧ 0 ≤ inner ℝ n v ∧ ∀ y ∈ P, inner ℝ n y ≤ inner ℝ n f₀ := by
  classical
  by_cases hv : v = 0
  · exfalso
    have hmem : f₀ + (δ / 2) • v ∈ P := by simpa [hv] using hf₀P
    exact hray (δ / 2) (by positivity) (by linarith) hmem
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let C : Set V := {w : V | ‖w‖ = 1 ∧ 0 ≤ inner ℝ w v}
  have hC_cpt : IsCompact C := by
    have hcl_sphere : IsClosed {w : V | ‖w‖ = 1} := isClosed_eq continuous_norm continuous_const
    have hsphere_sub : {w : V | ‖w‖ = 1} ⊆ closedBall (0 : V) 1 := by
      intro w hw
      dsimp [closedBall]
      rw [dist_eq_norm, sub_zero]
      exact le_of_eq hw
    have hcpt_sphere : IsCompact {w : V | ‖w‖ = 1} :=
      IsCompact.of_isClosed_subset (isCompact_closedBall (0 : V) 1) hcl_sphere hsphere_sub
    have hcl_half : IsClosed {w : V | 0 ≤ inner ℝ w v} := by
      apply isClosed_le continuous_const
      fun_prop
    have hC_eq : C = {w : V | 0 ≤ inner ℝ w v} ∩ {w : V | ‖w‖ = 1} := by
      ext w
      simp [C, and_comm]
    have hclC' : IsClosed ({w : V | 0 ≤ inner ℝ w v} ∩ {w : V | ‖w‖ = 1}) :=
      hcl_half.inter hcl_sphere
    rw [hC_eq]
    exact IsCompact.of_isClosed_subset hcpt_sphere hclC' (by intro w hw; exact hw.2)
  -- a strict separation of the point `f₀ + εv` from `P` gives a unit vector whose inner
  -- product with `v` is positive and whose defect over `P` is at most `ε * ‖v‖`
  have hsep : ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∃ w : V,
      ‖w‖ = 1 ∧ 0 < inner ℝ w v ∧ ∀ y ∈ P, inner ℝ w (y - f₀) ≤ ε * ‖v‖ := by
    intro ε hε0 hεδ
    have hxε : f₀ + ε • v ∉ P := hray ε hε0 hεδ
    rcases strict_separate_point_of_not_mem (P := P) hPconv hPcpt.isClosed hxε ⟨f₀, hf₀P⟩ with
      ⟨m, hmne, hmsep⟩
    have hmv : 0 < inner ℝ m v := by
      have h1 := hmsep f₀ hf₀P
      have h2 : inner ℝ m (f₀ + ε • v) = inner ℝ m f₀ + ε * inner ℝ m v := by
        rw [inner_add_right, inner_smul_right]
      have hdiff : 0 < ε * inner ℝ m v := by
        have := sub_pos.mpr h1
        rw [h2] at this
        linarith
      exact (mul_pos_iff_of_pos_left hε0).mp hdiff
    let w : V := ‖m‖⁻¹ • m
    have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hmne
    have hw_unit : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, norm_inv, norm_norm]
      field_simp [hmpos.ne']
    have hwv : 0 < inner ℝ w v := by
      dsimp [w]
      rw [inner_smul_left]
      have hcv : 0 < ‖m‖⁻¹ := inv_pos.mpr hmpos
      exact mul_pos hcv hmv
    refine ⟨w, hw_unit, hwv, ?_⟩
    intro y hy
    have hle' : inner ℝ m (y - f₀) < ε * inner ℝ m v := by
      have h3 : inner ℝ m (f₀ + ε • v) - inner ℝ m f₀ = ε * inner ℝ m v := by
        rw [inner_add_right, inner_smul_right]
        ring
      have hmsep_y := hmsep y hy
      calc
        inner ℝ m (y - f₀) = inner ℝ m y - inner ℝ m f₀ := by rw [inner_sub_right]
        _ < inner ℝ m (f₀ + ε • v) - inner ℝ m f₀ := by linarith
        _ = ε * inner ℝ m v := h3
    have hwy : inner ℝ w (y - f₀) = ‖m‖⁻¹ * inner ℝ m (y - f₀) := by
      simp [w, inner_smul_left]
    rw [hwy]
    calc
      ‖m‖⁻¹ * inner ℝ m (y - f₀) ≤ ‖m‖⁻¹ * (ε * inner ℝ m v) := by
        exact mul_le_mul_of_nonneg_left hle'.le (inv_nonneg.mpr hmpos.le)
      _ = ε * (‖m‖⁻¹ * inner ℝ m v) := by ring
      _ = ε * inner ℝ w v := by
        congr 1
        simp [w, inner_smul_left]
      _ ≤ ε * ‖v‖ := by
        have hCS : inner ℝ w v ≤ ‖w‖ * ‖v‖ := real_inner_le_norm w v
        calc
          ε * inner ℝ w v ≤ ε * (‖w‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left hCS (le_of_lt hε0)
          _ = ε * ‖v‖ := by
            rw [hw_unit]
            ring
  -- `E c` : unit vectors with `0 ≤ ⟪·,v⟫` whose defect over `P` is bounded by `c`
  let E : ℝ → Set V := fun c => {w : V | w ∈ C ∧ ∀ y ∈ P, inner ℝ w (y - f₀) ≤ c}
  have hclC : IsClosed C := by
    have hcl_sphere : IsClosed {w : V | ‖w‖ = 1} := isClosed_eq continuous_norm continuous_const
    have hcl_half : IsClosed {w : V | 0 ≤ inner ℝ w v} := by
      apply isClosed_le continuous_const
      fun_prop
    have hC_eq : C = {w : V | ‖w‖ = 1} ∩ {w : V | 0 ≤ inner ℝ w v} := by
      ext w
      simp [C, and_comm]
    rw [hC_eq]
    exact hcl_sphere.inter hcl_half
  have hE_closed : ∀ c : ℝ, IsClosed (E c) := by
    intro c
    have hcl_cond : IsClosed {w : V | ∀ y ∈ P, inner ℝ w (y - f₀) ≤ c} := by
      have hset : {w : V | ∀ y ∈ P, inner ℝ w (y - f₀) ≤ c} =
          ⋂ y ∈ P, {w : V | inner ℝ w (y - f₀) ≤ c} := by
        ext w
        simp
      rw [hset]
      refine isClosed_biInter ?_
      intro y hy
      refine isClosed_le ?_ continuous_const
      fun_prop
    have hE_eq : E c = C ∩ {w : V | ∀ y ∈ P, inner ℝ w (y - f₀) ≤ c} := by
      ext w
      simp [E]
    rw [hE_eq]
    exact hclC.inter hcl_cond
  have hE_cpt : ∀ c : ℝ, IsCompact (E c) := fun c =>
    IsCompact.of_isClosed_subset hC_cpt (hE_closed c) (by intro w hw; exact hw.1)
  have hE_mono : Monotone E := by
    intro c₁ c₂ hc w hw
    refine ⟨hw.1, ?_⟩
    intro y hy
    exact le_trans (hw.2 y hy) hc
  -- decreasing chain of nonempty compact sets; Cantor's intersection theorem gives the
  -- supporting functional we are after
  let t : ℕ → Set V := fun n => E ((δ / (n + 1 : ℝ)) * ‖v‖)
  have htd : ∀ n, t (n + 1) ⊆ t n := by
    intro n
    apply hE_mono
    apply mul_le_mul_of_nonneg_right ?_ hvpos.le
    have hd1 : 0 < (↑n + 1 : ℝ) := by positivity
    have hle : (↑n + 1 : ℝ) ≤ ↑(n + 1) + 1 := by
      norm_num [Nat.cast_add, Nat.cast_one]
    exact div_le_div_of_nonneg_left hδ.le hd1 hle
  have ht0cpt : IsCompact (t 0) := by
    simpa [t] using hE_cpt ((δ / (0 + 1 : ℝ)) * ‖v‖)
  have htcl : ∀ n, IsClosed (t n) := fun n => hE_closed ((δ / (n + 1 : ℝ)) * ‖v‖)
  have htn : ∀ n, (t n).Nonempty := by
    intro n
    have hε0 : 0 < δ / (n + 1 : ℝ) := by positivity
    have hεle : δ / (n + 1 : ℝ) ≤ δ := by
      rw [div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))]
      have h1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
      have : δ * (1 : ℝ) ≤ δ * (n + 1 : ℝ) := mul_le_mul_of_nonneg_left h1 hδ.le
      simpa using this
    rcases hsep (δ / (n + 1 : ℝ)) hε0 hεle with ⟨w, hw1, hwv0, hwle⟩
    refine ⟨w, ?_⟩
    exact ⟨⟨hw1, le_of_lt hwv0⟩, hwle⟩
  obtain ⟨nstar, hnstar⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0cpt htcl
  have hnstar_t : ∀ n : ℕ, nstar ∈ t n := fun n => Set.mem_iInter.mp hnstar n
  have hnstarC : nstar ∈ C := by
    have hsub : t 0 ⊆ C := by
      intro w hw
      exact hw.1
    exact hsub (hnstar_t 0)
  have hnstar_unit : ‖nstar‖ = 1 := hnstarC.1
  have hnstar_v : 0 ≤ inner ℝ nstar v := hnstarC.2
  have hnstar_ne : nstar ≠ 0 := by
    intro h0
    rw [h0] at hnstar_unit
    norm_num at hnstar_unit
  have hle0 : ∀ y ∈ P, inner ℝ nstar (y - f₀) ≤ 0 := by
    intro y hy
    by_contra hnot
    have hval : 0 < inner ℝ nstar (y - f₀) := lt_of_not_ge hnot
    obtain ⟨k, hk⟩ := exists_nat_gt (δ * ‖v‖ / inner ℝ nstar (y - f₀))
    have hk1 : δ * ‖v‖ / inner ℝ nstar (y - f₀) < (k + 1 : ℝ) :=
      lt_trans hk (by exact_mod_cast (Nat.lt_succ_self k) : (k : ℝ) < (k + 1 : ℝ))
    have hδv_lt : δ * ‖v‖ < inner ℝ nstar (y - f₀) * (k + 1 : ℝ) := by
      simpa [mul_comm] using ((div_lt_iff₀ hval).mp hk1)
    have hval_le : inner ℝ nstar (y - f₀) ≤ (δ / (k + 1 : ℝ)) * ‖v‖ := (hnstar_t k).2 y hy
    have hsmall : (δ / (k + 1 : ℝ)) * ‖v‖ < inner ℝ nstar (y - f₀) := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ (by positivity : 0 < (k + 1 : ℝ))).mpr hδv_lt
    linarith
  refine ⟨nstar, hnstar_ne, hnstar_v, ?_⟩
  intro y hy
  have h : inner ℝ nstar (y - f₀) ≤ 0 := hle0 y hy
  rw [inner_sub_right] at h
  linarith

end

/-- The requested statement: any point of the smear `P + [0,1]·v` outside the compact convex
set `P` lies in a prism over a supporting face of `P` in a direction `n` with `0 ≤ ⟪n,v⟫`. -/
theorem smear_frontier_cover {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    (P : Set V) (hPconv : Convex ℝ P) (hPcpt : IsCompact P) (v x : V)
    (hxS : ∃ p ∈ P, ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v)
    (hxP : x ∉ P) :
    ∃ n : V, n ≠ 0 ∧ 0 ≤ inner ℝ n v ∧
      ∃ f ∈ {x ∈ P | ∀ y ∈ P, inner ℝ n y ≤ inner ℝ n x},
        ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v := by
  classical
  let S : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ x - s • v ∈ P}
  have hS_ne : S.Nonempty := by
    rcases hxS with ⟨p, hpP, t, ht, hxt⟩
    refine ⟨t, ht, ?_⟩
    rw [hxt]
    abel_nf
    exact hpP
  have hφcont : Continuous (fun s : ℝ => x - s • v) := by fun_prop
  have hS_eq : S = (fun s : ℝ => x - s • v) ⁻¹' P ∩ Set.Icc (0 : ℝ) 1 := by
    ext s
    simp [S, and_comm]
  have hS_cl : IsClosed S := by
    rw [hS_eq]
    exact IsClosed.inter (hPcpt.isClosed.preimage hφcont) isClosed_Icc
  have hS_cpt : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hS_cl (by intro s hs; exact hs.1)
  obtain ⟨a, haIsLeast⟩ := hS_cpt.exists_isLeast hS_ne
  have haS : a ∈ S := haIsLeast.1
  have ha_min : ∀ s ∈ S, a ≤ s := haIsLeast.2
  have ha01 : a ∈ Set.Icc (0 : ℝ) 1 := haS.1
  -- the least parameter `a` is strictly positive because `0 ∉ S` (as `x ∉ P`)
  have ha0 : 0 < a := by
    have hle0 : 0 ≤ a := ha01.1
    have hne : a ≠ 0 := by
      intro ha0eq
      apply hxP
      have hmem : x - (0 : ℝ) • v ∈ P := by
        simpa [ha0eq] using haS.2
      simpa using hmem
    exact lt_of_le_of_ne hle0 hne.symm
  let f₀ : V := x - a • v
  have hf₀P : f₀ ∈ P := by
    dsimp [f₀]
    exact haS.2
  -- the open `v`-ray from `f₀` (up to size `a`) leaves `P`
  have hray : ∀ ε : ℝ, 0 < ε → ε ≤ a → f₀ + ε • v ∉ P := by
    intro ε hε0 hεa hmem
    have hmem' : x - (a - ε) • v ∈ P := by
      have heq : x - (a - ε) • v = f₀ + ε • v := by
        calc
          x - (a - ε) • v = x - a • v + ε • v := by
            rw [sub_smul]
            abel
          _ = f₀ + ε • v := by
            simp [f₀]
      rw [heq]
      exact hmem
    have hεinS : (a - ε) ∈ S := by
      refine ⟨?_, hmem'⟩
      constructor
      · linarith [hεa]
      · linarith [hε0, ha01.2]
    have hc : a ≤ a - ε := ha_min (a - ε) hεinS
    linarith
  rcases exists_supporting_functional_vnonneg (P := P) hPconv hPcpt v f₀ hf₀P a ha0 hray with
    ⟨n, hnne, hnv, hnsup⟩
  refine ⟨n, hnne, hnv, ?_⟩
  refine ⟨f₀, ?_, ?_⟩
  · refine ⟨hf₀P, ?_⟩
    intro y hy
    exact hnsup y hy
  · refine ⟨a, ha01, ?_⟩
    dsimp [f₀]
    abel

end Commons.Geometry.Convex.Hadwiger