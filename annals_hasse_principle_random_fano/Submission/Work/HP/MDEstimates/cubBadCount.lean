import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.BadDefs
import Submission.Work.Q44Geom.latW_count
import Submission.Work.HP.num_lattices
import Submission.Work.HP.minkowski_upper
import Submission.Work.HP.MDEstimates.detL_le_prod_lam
import Submission.Work.HP.lam_basic
import Submission.Work.HP.ballCount_le_pow_rk

/-!
# `Work.HP.MDEstimates.cubBadCount`

For a homogeneous cubic `B` in five variables with no linear factor and whose invariance
lattice `W = latW B = (invSub B) ∩ ℤ⁵` has rank `2`, the number of primitive rank-`3`
sublattices `L ⊇ W` on which `B` vanishes and whose successive minima satisfy
`λ_{j+1}(L) ≤ s j` is `≪ (s 0 * s 1 * s 2)^3`.

The proof is purely a lattice count: it splits the lattices `L` according to how short a
vector outside the rational span `W_ℚ = ratSpan W` they contain.

* If `L` contains `y ∉ W_ℚ` with `‖y‖ ≤ s 0`, then `L` is the saturation of `W + ℤ y`, so
  `L ↦ y` is injective and there are `≪ s 0^5` such lattices.
* Similarly, if `L` contains `y ∉ W_ℚ` with `‖y‖ ≤ s 1` (but none with `‖y‖ ≤ s 0`), then
  `L ↦ y` is injective and there are `≪ s 1^5` such lattices.
* Otherwise every vector of `L` of norm `≤ s 1` lies in `W`; then `λ₁(W) ≤ s 0` and
  `λ₂(W) ≤ s 1`, and the fibre count of the paper's "number lattices" lemma bounds the
  number of rank-`3` primitive `L ⊇ W` with `λ₃(L) ≤ s 2` by `≪ s 2^3 · detL W ≤ s 2^3 s 0 s 1`.

Finally `s 0^5`, `s 1^5 ≤ (s 0 s 1 s 2)^3` and `s 2^3 s 0 s 1 ≤ (s 0 s 1 s 2)^3` because
`1 ≤ s 0 ≤ s 1 ≤ s 2`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open MvPolynomial

theorem cubBadCount : ∃ C : ℝ, 0 < C ∧ ∀ (B : MvPolynomial (Fin 5) ℚ),
    B.IsHomogeneous 3 → B ≠ 0 →
    (∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) →
    Work.HP.rk (Work.Q44Geom.latW B) = 2 →
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
    (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
        (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0) ∧
        Work.Q44Geom.latW B ≤ L} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ C * (s 0 * s 1 * s 2) ^ 3 := by
  classical
  -- ### constants
  obtain ⟨Kb, hKbpos, hKb⟩ := Work.HP.ballCount_le_pow_rk (ι := Fin 5)
  obtain ⟨Kmk0, hKmk0pos, hmink0⟩ := Work.HP.minkowski_upper (Fin 5)
  set Kmk : ℝ := max Kmk0 1 with hKmkdef
  have hKmkpos : (0 : ℝ) < Kmk := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (j + 1)) ≤ Kmk * Work.HP.detL L :=
    fun L => le_trans (hmink0 L)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.HP.detL_nonneg L))
  refine ⟨2 ^ 5 * Kb + 2 ^ 5 * Kb + 16 ^ 5 * Kmk, by positivity, ?_⟩
  intro B hB hB0 hnolin hWrk2 s hs0 hs01 hs12
  -- ### the counting set
  set W : Submodule ℤ (Fin 5 → ℤ) := Work.Q44Geom.latW B with hWdef
  have hWprim : Work.HP.IsPrimLat W := by rw [hWdef]; exact Work.Q44Geom.isPrimLat_latW B
  have hWrk : Work.HP.rk W = 2 := by rw [hWdef]; exact hWrk2
  have hs0n : (0 : ℝ) ≤ s 0 := le_trans zero_le_one hs0
  have hs1 : (1 : ℝ) ≤ s 1 := le_trans hs0 hs01
  have hs1n : (0 : ℝ) ≤ s 1 := le_trans zero_le_one hs1
  have hs2 : (1 : ℝ) ≤ s 2 := le_trans hs1 hs12
  have hs2n : (0 : ℝ) ≤ s 2 := le_trans zero_le_one hs2
  set A : Set (Submodule ℤ (Fin 5 → ℤ)) :=
    {L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
      (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
      (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0) ∧
      W ≤ L} with hAdef
  -- ### a lattice containing `W` and a vector outside `W_ℚ` is the saturation of both
  have key : ∀ (L : Submodule ℤ (Fin 5 → ℤ)), Work.HP.IsPrimLat L → Work.HP.rk L = 3 →
      W ≤ L → ∀ y : Fin 5 → ℤ, y ∈ L → Work.Q44Geom.toRatLM y ∉ Work.Q44Geom.ratSpan W →
      L = Submodule.comap Work.Q44Geom.toRatLM
            ((Work.Q44Geom.ratSpan W ⊔ Submodule.span ℚ {Work.Q44Geom.toRatLM y}).restrictScalars ℤ) := by
    intro L hLprim hLrk hWL y hy hyW
    have hW_ne : Work.Q44Geom.toRatLM y ≠ 0 := by
      intro h0; exact hyW (h0 ▸ Submodule.zero_mem _)
    have hle : Work.Q44Geom.ratSpan W ⊔ Submodule.span ℚ {Work.Q44Geom.toRatLM y}
        ≤ Work.Q44Geom.ratSpan L := by
      refine sup_le (Work.Q44Geom.ratSpan_mono hWL) ?_
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
    have hinf : Work.Q44Geom.ratSpan W ⊓ Submodule.span ℚ {Work.Q44Geom.toRatLM y} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx2
      by_cases hc0 : c = 0
      · rw [← hc, hc0, zero_smul]
      · exfalso
        have hmem : Work.Q44Geom.toRatLM y ∈ Work.Q44Geom.ratSpan W := by
          have h := (Work.Q44Geom.ratSpan W).smul_mem c⁻¹ hx1
          rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
          exact h
        exact hyW hmem
    have hfr : Module.finrank ℚ
        ↥(Work.Q44Geom.ratSpan W ⊔ Submodule.span ℚ {Work.Q44Geom.toRatLM y}) = 3 := by
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Work.Q44Geom.ratSpan W)
        (Submodule.span ℚ {Work.Q44Geom.toRatLM y})
      rw [hinf, finrank_bot ℚ (Fin 5 → ℚ), add_zero, Work.Q44Geom.ratSpan_finrank_general W, hWrk,
        finrank_span_singleton hW_ne] at hsup
      omega
    have heq := Submodule.eq_of_le_of_finrank_eq hle
      (by rw [hfr, Work.Q44Geom.ratSpan_finrank_general L, hLrk])
    ext v
    rw [Submodule.mem_comap, heq]
    exact Work.Q44Geom.sat_span L hLprim v
  -- ### the three pieces
  let P0 : (Submodule ℤ (Fin 5 → ℤ)) → Prop := fun L =>
    ∃ y : Fin 5 → ℤ, y ∈ L ∧ Work.Q44Geom.toRatLM y ∉ Work.Q44Geom.ratSpan W ∧
      Work.HP.eNorm y ≤ s 0
  let P1 : (Submodule ℤ (Fin 5 → ℤ)) → Prop := fun L =>
    ∃ y : Fin 5 → ℤ, y ∈ L ∧ Work.Q44Geom.toRatLM y ∉ Work.Q44Geom.ratSpan W ∧
      Work.HP.eNorm y ≤ s 1
  let Y0 : (Submodule ℤ (Fin 5 → ℤ)) → (Fin 5 → ℤ) :=
    fun L => if h : P0 L then Classical.choose h else 0
  let Y1 : (Submodule ℤ (Fin 5 → ℤ)) → (Fin 5 → ℤ) :=
    fun L => if h : P1 L then Classical.choose h else 0
  have hY0 : ∀ L, P0 L → Y0 L ∈ L ∧
      Work.Q44Geom.toRatLM (Y0 L) ∉ Work.Q44Geom.ratSpan W ∧ Work.HP.eNorm (Y0 L) ≤ s 0 := by
    intro L h
    have h1 : Y0 L = Classical.choose h := by dsimp only [Y0]; rw [dif_pos h]
    rw [h1]; exact Classical.choose_spec h
  have hY1 : ∀ L, P1 L → Y1 L ∈ L ∧
      Work.Q44Geom.toRatLM (Y1 L) ∉ Work.Q44Geom.ratSpan W ∧ Work.HP.eNorm (Y1 L) ≤ s 1 := by
    intro L h
    have h1 : Y1 L = Classical.choose h := by dsimp only [Y1]; rw [dif_pos h]
    rw [h1]; exact Classical.choose_spec h
  set C1 : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | L ∈ A ∧ P0 L} with hC1
  set C2 : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | L ∈ A ∧ ¬ P0 L ∧ P1 L} with hC2
  set C3 : Set (Submodule ℤ (Fin 5 → ℤ)) := {L | L ∈ A ∧ ¬ P1 L} with hC3
  have hcover : A ⊆ C1 ∪ C2 ∪ C3 := by
    intro L hL
    by_cases h0 : P0 L
    · exact Or.inl (Or.inl ⟨hL, h0⟩)
    · by_cases h1 : P1 L
      · exact Or.inl (Or.inr ⟨hL, h0, h1⟩)
      · exact Or.inr ⟨hL, h1⟩
  -- ### the first two pieces inject into balls
  have hinj0 : Set.InjOn Y0 C1 := by
    intro L hL L' hL' hy
    obtain ⟨hLA, h0⟩ := hL
    obtain ⟨hLA', h0'⟩ := hL'
    rw [key L hLA.1 hLA.2.1 hLA.2.2.2.2 (Y0 L) (hY0 L h0).1 (hY0 L h0).2.1,
        key L' hLA'.1 hLA'.2.1 hLA'.2.2.2.2 (Y0 L') (hY0 L' h0').1 (hY0 L' h0').2.1, hy]
  have hinj1 : Set.InjOn Y1 C2 := by
    intro L hL L' hL' hy
    obtain ⟨hLA, -, h1⟩ := hL
    obtain ⟨hLA', -, h1'⟩ := hL'
    rw [key L hLA.1 hLA.2.1 hLA.2.2.2.2 (Y1 L) (hY1 L h1).1 (hY1 L h1).2.1,
        key L' hLA'.1 hLA'.2.1 hLA'.2.2.2.2 (Y1 L') (hY1 L' h1').1 (hY1 L' h1').2.1, hy]
  have hballdef : ∀ T : ℝ, (0 : ℝ) ≤ T →
      (({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ Kb * (T + 1) ^ 5 := by
    intro T hT
    have h := hKb (⊤ : Submodule ℤ (Fin 5 → ℤ)) T hT
    have hrk : Work.HP.rk (⊤ : Submodule ℤ (Fin 5 → ℤ)) = 5 := by
      change Module.finrank ℤ ↥(⊤ : Submodule ℤ (Fin 5 → ℤ)) = 5
      rw [finrank_top]
      exact Module.finrank_fin_fun ℤ
    have hset : ({v : Fin 5 → ℤ | v ∈ (⊤ : Submodule ℤ (Fin 5 → ℤ)) ∧
        Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)) = {v : Fin 5 → ℤ | Work.HP.eNorm v ≤ T} := by
      ext v; simp
    rw [Work.HP.ballCount, hset, hrk] at h
    exact h
  have hC1bound : ((C1 : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ Kb * 2 ^ 5 * (s 0) ^ 5 := by
    have hstep : C1.ncard ≤ ({y : Fin 5 → ℤ | Work.HP.eNorm y ≤ s 0} : Set (Fin 5 → ℤ)).ncard :=
      Set.ncard_le_ncard_of_injOn Y0 (fun L hL => (hY0 L hL.2).2.2) hinj0
        (Work.HP.MDBasic.finite_eNorm_le (s 0))
    have hball := hballdef (s 0) hs0n
    have h2 : (({y : Fin 5 → ℤ | Work.HP.eNorm y ≤ s 0} : Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ Kb * 2 ^ 5 * (s 0) ^ 5 := by
      refine le_trans hball ?_
      have hle : s 0 + 1 ≤ 2 * s 0 := by linarith
      have hp : (s 0 + 1) ^ 5 ≤ (2 * s 0) ^ 5 :=
        pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ s 0 + 1) hle 5
      calc Kb * (s 0 + 1) ^ 5 ≤ Kb * (2 * s 0) ^ 5 := mul_le_mul_of_nonneg_left hp hKbpos.le
      _ = Kb * 2 ^ 5 * (s 0) ^ 5 := by ring
    exact le_trans (by exact_mod_cast hstep) h2
  have hC2bound : ((C2 : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ Kb * 2 ^ 5 * (s 1) ^ 5 := by
    have hstep : C2.ncard ≤ ({y : Fin 5 → ℤ | Work.HP.eNorm y ≤ s 1} : Set (Fin 5 → ℤ)).ncard :=
      Set.ncard_le_ncard_of_injOn Y1 (fun L hL => (hY1 L hL.2.2).2.2) hinj1
        (Work.HP.MDBasic.finite_eNorm_le (s 1))
    have hball := hballdef (s 1) hs1n
    have h2 : (({y : Fin 5 → ℤ | Work.HP.eNorm y ≤ s 1} : Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ Kb * 2 ^ 5 * (s 1) ^ 5 := by
      refine le_trans hball ?_
      have hle : s 1 + 1 ≤ 2 * s 1 := by linarith
      have hp : (s 1 + 1) ^ 5 ≤ (2 * s 1) ^ 5 :=
        pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ s 1 + 1) hle 5
      calc Kb * (s 1 + 1) ^ 5 ≤ Kb * (2 * s 1) ^ 5 := mul_le_mul_of_nonneg_left hp hKbpos.le
      _ = Kb * 2 ^ 5 * (s 1) ^ 5 := by ring
    exact le_trans (by exact_mod_cast hstep) h2
  -- ### finiteness of the fibre set and the fibre bound
  have hFfin : ({L : Submodule ℤ (Fin 5 → ℤ) | W ≤ L ∧ Work.HP.IsPrimLat L ∧
      Work.HP.rk L = 3 ∧ Work.HP.lam L 3 ≤ s 2} : Set (Submodule ℤ (Fin 5 → ℤ))).Finite := by
    let P2 : (Submodule ℤ (Fin 5 → ℤ)) → Prop := fun L =>
      ∃ y : Fin 5 → ℤ, y ∈ L ∧ Work.Q44Geom.toRatLM y ∉ Work.Q44Geom.ratSpan W ∧
        Work.HP.eNorm y ≤ s 2
    let Y2 : (Submodule ℤ (Fin 5 → ℤ)) → (Fin 5 → ℤ) :=
      fun L => if h : P2 L then Classical.choose h else 0
    have hY2 : ∀ L, P2 L → Y2 L ∈ L ∧
        Work.Q44Geom.toRatLM (Y2 L) ∉ Work.Q44Geom.ratSpan W ∧ Work.HP.eNorm (Y2 L) ≤ s 2 := by
      intro L h
      have h1 : Y2 L = Classical.choose h := by dsimp only [Y2]; rw [dif_pos h]
      rw [h1]; exact Classical.choose_spec h
    have hex : ∀ L ∈ ({L : Submodule ℤ (Fin 5 → ℤ) | W ≤ L ∧ Work.HP.IsPrimLat L ∧
        Work.HP.rk L = 3 ∧ Work.HP.lam L 3 ≤ s 2} : Set (Submodule ℤ (Fin 5 → ℤ))), P2 L := by
      intro L hL
      obtain ⟨hWL, hLprim, hLrk, hlam3⟩ := hL
      obtain ⟨f, hfL, hfind, hfb⟩ := exists_linIndep_le_lam L (m := 3) (by simp [hLrk])
      by_contra hcon
      have hcon' : ∀ y : Fin 5 → ℤ, y ∈ L → Work.HP.eNorm y ≤ s 2 →
          Work.Q44Geom.toRatLM y ∈ Work.Q44Geom.ratSpan W := by
        intro y hy hy2
        by_contra hny
        exact hcon ⟨y, hy, hny, hy2⟩
      have hmemW : ∀ i : Fin 3, f i ∈ W := by
        intro i
        have hi : Work.HP.eNorm (f i) ≤ s 2 :=
          le_trans (hfb i)
            (le_trans (Work.HP.lam_mono L (by have := i.isLt; omega) (by rw [hLrk])) hlam3)
        exact (Work.Q44Geom.sat_span W hWprim (f i)).mpr (hcon' (f i) (hfL i) hi)
      have hgLI : LinearIndependent ℤ (fun i : Fin 3 => (⟨f i, hmemW i⟩ : ↥W)) := by
        refine LinearIndependent.of_comp W.subtype ?_
        have hcomp : (⇑W.subtype ∘ (fun i : Fin 3 => (⟨f i, hmemW i⟩ : ↥W))) = f := by
          funext i; rfl
        rw [hcomp]; exact hfind
      have hcard := hgLI.fintype_card_le_finrank
      rw [Fintype.card_fin] at hcard
      have hrk : Work.HP.rk W = Module.finrank ℤ ↥W := rfl
      omega
    have hinj2 : Set.InjOn Y2 ({L : Submodule ℤ (Fin 5 → ℤ) | W ≤ L ∧ Work.HP.IsPrimLat L ∧
        Work.HP.rk L = 3 ∧ Work.HP.lam L 3 ≤ s 2} : Set (Submodule ℤ (Fin 5 → ℤ))) := by
      intro L hL L' hL' hy
      have hWL : W ≤ L := hL.1
      have hLprim : Work.HP.IsPrimLat L := hL.2.1
      have hLrk : Work.HP.rk L = 3 := hL.2.2.1
      have hWL' : W ≤ L' := hL'.1
      have hLprim' : Work.HP.IsPrimLat L' := hL'.2.1
      have hLrk' : Work.HP.rk L' = 3 := hL'.2.2.1
      rw [key L hLprim hLrk hWL (Y2 L) (hY2 L (hex L hL)).1 (hY2 L (hex L hL)).2.1,
          key L' hLprim' hLrk' hWL' (Y2 L') (hY2 L' (hex L' hL')).1 (hY2 L' (hex L' hL')).2.1, hy]
    exact Set.Finite.of_injOn (f := Y2) (fun L hL => (hY2 L (hex L hL)).2.2) hinj2
      (Work.HP.MDBasic.finite_eNorm_le (s 2))
  have hfib : (({L : Submodule ℤ (Fin 5 → ℤ) | W ≤ L ∧ Work.HP.IsPrimLat L ∧
      Work.HP.rk L = 3 ∧ Work.HP.lam L 3 ≤ s 2} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ 16 ^ 5 * Kmk * (s 2) ^ 3 * Work.HP.detL W := by
    have h := Work.HP.fiber_count (ι := Fin 5) Kmk hKmkpos.le W hWprim (s 2) hs2 hmink
    rw [hWrk] at h
    simp only [Fintype.card_fin, Nat.reduceAdd, Nat.reduceSub] at h
    exact h
  -- ### the third piece
  have hC3sub : C3 ⊆ {L : Submodule ℤ (Fin 5 → ℤ) | W ≤ L ∧ Work.HP.IsPrimLat L ∧
      Work.HP.rk L = 3 ∧ Work.HP.lam L 3 ≤ s 2} := by
    intro L hL
    obtain ⟨hLA, -⟩ := hL
    exact ⟨hLA.2.2.2.2, hLA.1, hLA.2.1, by simpa using hLA.2.2.1 ⟨2, by norm_num⟩⟩
  have hC3bound : ((C3 : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ 16 ^ 5 * Kmk * (s 2) ^ 3 * (s 0 * s 1) := by
    have hstep := Set.ncard_le_ncard hC3sub hFfin
    by_cases hne : (C3 : Set (Submodule ℤ (Fin 5 → ℤ))).Nonempty
    · obtain ⟨L0, hL0⟩ := hne
      obtain ⟨hL0A, hL0not⟩ := hL0
      obtain ⟨hL0prim, hL0rk, hL0lam, -, -⟩ := hL0A
      have hnot : ∀ y : Fin 5 → ℤ, y ∈ L0 →
          Work.Q44Geom.toRatLM y ∉ Work.Q44Geom.ratSpan W → s 1 < Work.HP.eNorm y := by
        intro y hy hyW
        by_contra hcon
        push_neg at hcon
        exact hL0not ⟨y, hy, hyW, hcon⟩
      have hlam1 : Work.HP.lam W 1 ≤ s 0 := by
        obtain ⟨f, hfL, hfind, hfb⟩ := exists_linIndep_le_lam L0 (m := 1) (by simp [hL0rk])
        have hmem : f 0 ∈ W := by
          by_contra hcon
          have hc2 : Work.Q44Geom.toRatLM (f 0) ∉ Work.Q44Geom.ratSpan W :=
            fun h => hcon ((Work.Q44Geom.sat_span W hWprim (f 0)).mpr h)
          have hlt : s 1 < Work.HP.eNorm (f 0) := hnot (f 0) (hfL 0) hc2
          have hle : Work.HP.eNorm (f 0) ≤ s 1 := by
            have h4 : Work.HP.lam L0 ((0 : Fin 1).val + 1) ≤ s 1 := by
              have h5 := hL0lam ⟨0, by norm_num⟩
              simpa using le_trans h5 hs01
            exact le_trans (hfb 0) h4
          exact absurd hle (not_le.mpr hlt)
        have hne0 : f 0 ≠ 0 := hfind.ne_zero 0
        refine le_trans (Work.HP.lam_one_le_eNorm W hmem hne0) ?_
        have h4 : Work.HP.lam L0 ((0 : Fin 1).val + 1) ≤ s 0 := hL0lam ⟨0, by norm_num⟩
        exact le_trans (hfb 0) h4
      have hlam2 : Work.HP.lam W 2 ≤ s 1 := by
        obtain ⟨f, hfL, hfind, hfb⟩ := exists_linIndep_le_lam L0 (m := 2) (by simp [hL0rk])
        have hmem : ∀ i : Fin 2, f i ∈ W := by
          intro i
          by_contra hcon
          have hc2 : Work.Q44Geom.toRatLM (f i) ∉ Work.Q44Geom.ratSpan W :=
            fun h => hcon ((Work.Q44Geom.sat_span W hWprim (f i)).mpr h)
          have hlt : s 1 < Work.HP.eNorm (f i) := hnot (f i) (hfL i) hc2
          have hle : Work.HP.eNorm (f i) ≤ s 1 := by
            have h4 : Work.HP.lam L0 (i.val + 1) ≤ s 1 := by
              fin_cases i
              · have h5 := hL0lam ⟨0, by norm_num⟩
                simpa using le_trans h5 hs01
              · exact hL0lam ⟨1, by norm_num⟩
            exact le_trans (hfb i) h4
          exact absurd hle (not_le.mpr hlt)
        have hfun : (![f 0, f 1] : Fin 2 → (Fin 5 → ℤ)) = f := by funext i; fin_cases i <;> rfl
        have hind : LinearIndependent ℤ ![f 0, f 1] := hfun ▸ hfind
        have hmax := Work.HP.lam_two_le_max W (hmem 0) (hmem 1) hind
        refine le_trans hmax (max_le ?_ ?_)
        · have h5 := hL0lam ⟨0, by norm_num⟩
          exact le_trans (hfb 0) (le_trans h5 hs01)
        · have h5 := hL0lam ⟨1, by norm_num⟩
          exact le_trans (hfb 1) h5
      have hdet : Work.HP.detL W ≤ s 0 * s 1 := by
        have h := detL_le_prod_lam W
        rw [hWrk, Finset.prod_range_succ, Finset.prod_range_one] at h
        refine le_trans h ?_
        refine mul_le_mul hlam1 hlam2 (Work.HP.lam_nonneg W 2) ?_
        exact le_trans (Work.HP.lam_nonneg W 1) hlam1
      calc ((C3 : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
          ≤ (({L : Submodule ℤ (Fin 5 → ℤ) | W ≤ L ∧ Work.HP.IsPrimLat L ∧
              Work.HP.rk L = 3 ∧ Work.HP.lam L 3 ≤ s 2} :
              Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by exact_mod_cast hstep
        _ ≤ 16 ^ 5 * Kmk * (s 2) ^ 3 * Work.HP.detL W := hfib
        _ ≤ 16 ^ 5 * Kmk * (s 2) ^ 3 * (s 0 * s 1) :=
            mul_le_mul_of_nonneg_left hdet (by positivity)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty, Nat.cast_zero]
      positivity
  -- ### arithmetic
  have hge1 : (1 : ℝ) ≤ s 0 * s 1 * s 2 := by
    have h01 : (1 : ℝ) ≤ s 0 * s 1 :=
      le_trans hs0 (by simpa using mul_le_mul_of_nonneg_left hs1 hs0n)
    exact le_trans h01 (le_mul_of_one_le_right (le_trans zero_le_one h01) hs2)
  have hprod0 : (s 0) ^ 3 ≤ s 0 * s 1 * s 2 := by
    have h : s 0 * s 0 ≤ s 1 * s 2 := mul_le_mul hs01 (le_trans hs01 hs12) hs0n hs1n
    calc (s 0) ^ 3 = s 0 * (s 0 * s 0) := by ring
      _ ≤ s 0 * (s 1 * s 2) := mul_le_mul_of_nonneg_left h hs0n
      _ = s 0 * s 1 * s 2 := by ring
  have hprod0' : (s 0) ^ 2 ≤ s 0 * s 1 * s 2 := by
    have h : s 0 ≤ s 1 * s 2 := by nlinarith [hs0, hs01, hs12, hs1n, hs2n]
    calc (s 0) ^ 2 = s 0 * s 0 := by ring
      _ ≤ s 0 * (s 1 * s 2) := mul_le_mul_of_nonneg_left h hs0n
      _ = s 0 * s 1 * s 2 := by ring
  have hS0 : (s 0) ^ 5 ≤ (s 0 * s 1 * s 2) ^ 3 := by
    have hb : (0 : ℝ) ≤ s 0 * s 1 * s 2 := by positivity
    calc (s 0) ^ 5 = (s 0) ^ 3 * (s 0) ^ 2 := by ring
      _ ≤ (s 0 * s 1 * s 2) * (s 0 * s 1 * s 2) :=
          mul_le_mul hprod0 hprod0' (by positivity) hb
      _ = (s 0 * s 1 * s 2) ^ 2 := by ring
      _ ≤ (s 0 * s 1 * s 2) ^ 3 := by
          calc (s 0 * s 1 * s 2) ^ 2 = (s 0 * s 1 * s 2) ^ 2 * 1 := by ring
            _ ≤ (s 0 * s 1 * s 2) ^ 2 * (s 0 * s 1 * s 2) :=
                mul_le_mul_of_nonneg_left hge1 (by positivity)
            _ = (s 0 * s 1 * s 2) ^ 3 := by ring
  have hS1 : (s 1) ^ 5 ≤ (s 0 * s 1 * s 2) ^ 3 := by
    have hs0s2 : s 1 ≤ s 0 * s 2 := by nlinarith [hs0, hs12, hs2n]
    have hp : s 1 * s 1 ≤ s 0 * s 1 * s 2 := by
      calc s 1 * s 1 = s 1 * s 1 := rfl
        _ ≤ s 1 * (s 0 * s 2) := mul_le_mul_of_nonneg_left hs0s2 hs1n
        _ = s 0 * s 1 * s 2 := by ring
    have hs1le : s 1 ≤ s 0 * s 1 * s 2 := by
      calc s 1 = 1 * s 1 := by ring
        _ ≤ s 1 * s 1 := mul_le_mul_of_nonneg_right hs1 hs1n
        _ ≤ s 0 * s 1 * s 2 := hp
    calc (s 1) ^ 5 = (s 1 * s 1) ^ 2 * (s 1) := by ring
      _ ≤ (s 0 * s 1 * s 2) ^ 2 * (s 0 * s 1 * s 2) :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) hp 2) hs1le (by positivity) (by positivity)
      _ = (s 0 * s 1 * s 2) ^ 3 := by ring
  have hS2 : s 0 * s 1 * (s 2) ^ 3 ≤ (s 0 * s 1 * s 2) ^ 3 := by
    have hge : (1 : ℝ) ≤ s 0 * s 1 :=
      le_trans hs0 (by simpa using mul_le_mul_of_nonneg_left hs1 hs0n)
    have hge2 : (1 : ℝ) ≤ (s 0 * s 1) ^ 2 := one_le_pow₀ hge
    calc s 0 * s 1 * (s 2) ^ 3 = 1 * (s 0 * s 1 * (s 2) ^ 3) := by ring
      _ ≤ (s 0 * s 1) ^ 2 * (s 0 * s 1 * (s 2) ^ 3) :=
          mul_le_mul_of_nonneg_right hge2 (by positivity)
      _ = (s 0 * s 1 * s 2) ^ 3 := by ring
  -- ### assembly
  have hC1fin : C1.Finite := Set.Finite.of_injOn (f := Y0)
    (fun L hL => (hY0 L hL.2).2.2) hinj0 (Work.HP.MDBasic.finite_eNorm_le (s 0))
  have hC2fin : C2.Finite := Set.Finite.of_injOn (f := Y1)
    (fun L hL => (hY1 L hL.2.2).2.2) hinj1 (Work.HP.MDBasic.finite_eNorm_le (s 1))
  have hC3fin : C3.Finite := hFfin.subset hC3sub
  have hUfin : (C1 ∪ C2 ∪ C3).Finite := (hC1fin.union hC2fin).union hC3fin
  have hAle : (A : Set (Submodule ℤ (Fin 5 → ℤ))).ncard
      ≤ (C1 ∪ C2 ∪ C3).ncard := Set.ncard_le_ncard hcover hUfin
  have hUle : (C1 ∪ C2 ∪ C3 : Set (Submodule ℤ (Fin 5 → ℤ))).ncard
      ≤ C1.ncard + C2.ncard + C3.ncard := by
    have h1 := Set.ncard_union_le (C1 : Set (Submodule ℤ (Fin 5 → ℤ)))
      (C2 : Set (Submodule ℤ (Fin 5 → ℤ)))
    have h2 := Set.ncard_union_le ((C1 ∪ C2 : Set (Submodule ℤ (Fin 5 → ℤ))))
      (C3 : Set (Submodule ℤ (Fin 5 → ℤ)))
    have h3 : ((C1 ∪ C2 : Set (Submodule ℤ (Fin 5 → ℤ)))).ncard ≤ C1.ncard + C2.ncard := h1
    omega
  have hA1 : Kb * 2 ^ 5 * (s 0) ^ 5 ≤ Kb * 2 ^ 5 * (s 0 * s 1 * s 2) ^ 3 :=
    mul_le_mul_of_nonneg_left hS0 (by positivity)
  have hA2 : Kb * 2 ^ 5 * (s 1) ^ 5 ≤ Kb * 2 ^ 5 * (s 0 * s 1 * s 2) ^ 3 :=
    mul_le_mul_of_nonneg_left hS1 (by positivity)
  have hA3 : (16 : ℝ) ^ 5 * Kmk * (s 2) ^ 3 * (s 0 * s 1)
      ≤ (16 : ℝ) ^ 5 * Kmk * (s 0 * s 1 * s 2) ^ 3 := by
    rw [show (16 : ℝ) ^ 5 * Kmk * (s 2) ^ 3 * (s 0 * s 1)
          = (16 : ℝ) ^ 5 * Kmk * ((s 2) ^ 3 * (s 0 * s 1)) by ring,
        show (16 : ℝ) ^ 5 * Kmk * (s 0 * s 1 * s 2) ^ 3
          = (16 : ℝ) ^ 5 * Kmk * ((s 0 * s 1 * s 2) ^ 3) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h' : (s 2) ^ 3 * (s 0 * s 1) = s 0 * s 1 * (s 2) ^ 3 := by ring
    rw [h']
    exact hS2
  calc ((A : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ ((C1 ∪ C2 ∪ C3 : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by exact_mod_cast hAle
    _ ≤ (C1.ncard : ℝ) + (C2.ncard : ℝ) + (C3.ncard : ℝ) := by exact_mod_cast hUle
    _ ≤ Kb * 2 ^ 5 * (s 0) ^ 5 + Kb * 2 ^ 5 * (s 1) ^ 5
          + 16 ^ 5 * Kmk * (s 2) ^ 3 * (s 0 * s 1) :=
        add_le_add (add_le_add hC1bound hC2bound) hC3bound
    _ ≤ Kb * 2 ^ 5 * (s 0 * s 1 * s 2) ^ 3 + Kb * 2 ^ 5 * (s 0 * s 1 * s 2) ^ 3
          + 16 ^ 5 * Kmk * (s 0 * s 1 * s 2) ^ 3 :=
        add_le_add (add_le_add hA1 hA2) hA3
    _ = (2 ^ 5 * Kb + 2 ^ 5 * Kb + 16 ^ 5 * Kmk) * (s 0 * s 1 * s 2) ^ 3 := by ring

end Work.HP.MDEstimates
