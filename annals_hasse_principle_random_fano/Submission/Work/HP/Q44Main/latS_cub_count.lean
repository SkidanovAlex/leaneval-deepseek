import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MDEstimates.cubLatAux
import Submission.Work.HP.MDEstimates.cubBadCount
import Submission.Work.HP.MDEstimates.cubInv_finrank_le
import Submission.Work.HP.MDEstimates.cubPlaneDirection
import Submission.Work.HP.MDEstimates.cubLevelForms
import Submission.Work.HP.MDEstimates.vanishRatSpanCub
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.BadDefs
import Submission.Work.Q44Geom.zero_count
import Submission.Work.Q44Geom.planeBoundFin
import Submission.Work.Q44Geom.complBasis
import Submission.Work.Q44Geom.levels
import Submission.Work.Q44Geom.ncard_le_planeSet_ncard
import Submission.Work.HP.Q44Main.cubGcdOne
import Submission.Work.HP.Q44Main.cubW3NoRk2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

open MvPolynomial

namespace Work.HP.Q44Main

/-! ## Elementary arithmetic -/

/-- `s 0 ^ 4 * s 1 ^ 4 ≤ (s 0 * s 1 * s 2) ^ 3` under `1 ≤ s 0 ≤ s 1 ≤ s 2`. -/
lemma pow_four_le_latS (s : Fin 3 → ℝ) (hs0 : 1 ≤ s 0) (hs01 : s 0 ≤ s 1) (hs12 : s 1 ≤ s 2) :
    s 0 ^ 4 * s 1 ^ 4 ≤ (s 0 * s 1 * s 2) ^ 3 := by
  have h1 : (1 : ℝ) ≤ s 1 := le_trans hs0 hs01
  have h2 : (1 : ℝ) ≤ s 2 := le_trans h1 hs12
  have hle : s 0 * s 1 ≤ s 2 ^ 3 := by
    have h4 : s 0 * s 1 ≤ s 2 * s 2 := by nlinarith
    have h5 : s 2 * s 2 ≤ s 2 ^ 3 := by nlinarith
    linarith
  calc s 0 ^ 4 * s 1 ^ 4 = (s 0 * s 1) ^ 3 * (s 0 * s 1) := by ring
    _ ≤ (s 0 * s 1) ^ 3 * s 2 ^ 3 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (s 0 * s 1 * s 2) ^ 3 := by ring

/-! ## The six level forms of a cubic in a basis `(w, b₁, b₂)` -/

/-- The six level forms of degree `≤ 2` of a cubic `B` in the basis `(w, b₁, b₂)`. -/
def levelFamLatS (b₁ b₂ : Fin 5 → ℚ) (w : Fin 3 → Fin 5 → ℚ) (B : MvPolynomial (Fin 5) ℚ) :
    {q : Fin 3 × Fin 3 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 2} → MvPolynomial (Fin 3) ℚ :=
  fun q => Work.Q44Geom.levelForm w b₁ b₂ B ![(q.1.1 : ℕ), (q.1.2 : ℕ)]

/-! ## The number of isotropic `3`-planes through a good pair is bounded -/

/-- For a nonzero homogeneous cubic `B` in five variables without a linear factor and a pair of
nonzero integral vectors `x, y` spanning a line on which `B` vanishes, with
`toRatLM x ∉ invSub B` or `toRatLM y ∉ invSub B`, the set of `3`-planes of `ℚ⁵` through
`toRatLM x` and `toRatLM y` on which `B` vanishes is finite with cardinality bounded by an
absolute constant. -/
theorem cubPlaneBoundMain : ∃ K : ℝ, 0 < K ∧ ∀ (B : MvPolynomial (Fin 5) ℚ),
    B.IsHomogeneous 3 → B ≠ 0 →
    (∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) →
    ∀ (x y : Fin 5 → ℤ), x ≠ 0 → y ≠ 0 →
    LinearIndependent ℚ ![Work.Q44Geom.toRatLM x, Work.Q44Geom.toRatLM y] →
    MvPolynomial.eval (Work.Q44Geom.toRatLM x) B = 0 →
    MvPolynomial.eval (Work.Q44Geom.toRatLM y) B = 0 →
    (∀ a c : ℚ,
      MvPolynomial.eval (a • Work.Q44Geom.toRatLM x + c • Work.Q44Geom.toRatLM y) B = 0) →
    (Work.Q44Geom.toRatLM x ∉ Work.Q44Geom.invSub B ∨
      Work.Q44Geom.toRatLM y ∉ Work.Q44Geom.invSub B) →
    (Work.HP.MDEstimates.CubPlaneSet B x y).Finite ∧
      ((Work.HP.MDEstimates.CubPlaneSet B x y).ncard : ℝ) ≤ K := by
  obtain ⟨Bnd, hBnd⟩ := Work.Q44Geom.planeBound
  refine ⟨(Bnd : ℝ) + 1, by positivity, ?_⟩
  intro B hBhom hBne hnolin x y _hx0 _hy0 hbind _hBx _hBy hline hnd
  set b₁ : Fin 5 → ℚ := Work.Q44Geom.toRatLM x with hb1def
  set b₂ : Fin 5 → ℚ := Work.Q44Geom.toRatLM y with hb2def
  have hℓ' : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) B = 0 := by
    intro u
    rw [hb1def, hb2def]
    exact hline (u 0) (u 1)
  obtain ⟨w, hw, hwspan⟩ := Work.Q44Geom.complBasis b₁ b₂ hbind
  -- the level forms are homogeneous of degree at most `4`
  have hdeg : ∀ q : {q : Fin 3 × Fin 3 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 2},
      ∃ d : ℕ, d ≤ 4 ∧ (levelFamLatS b₁ b₂ w B q).IsHomogeneous d := by
    intro q
    refine ⟨3 - ((q.1.1 : ℕ) + (q.1.2 : ℕ)), by omega, ?_⟩
    have h3 : ((![(q.1.1 : ℕ), (q.1.2 : ℕ)] : Fin 2 → ℕ) 0)
        + ((![(q.1.1 : ℕ), (q.1.2 : ℕ)] : Fin 2 → ℕ) 1) ≤ 3 := by
      have hq2 : (q.1.1 : ℕ) + (q.1.2 : ℕ) ≤ 2 := q.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    have hh := Work.HP.MDEstimates.levelForm_cubic_isHomogeneous w b₁ b₂ B hBhom
      ![(q.1.1 : ℕ), (q.1.2 : ℕ)] h3
    simpa [levelFamLatS, Matrix.cons_val_zero, Matrix.cons_val_one] using hh
  -- the six level forms have no common nonconstant divisor
  have hgcd : ∀ h : MvPolynomial (Fin 3) ℚ,
      (∀ q : {q : Fin 3 × Fin 3 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 2},
        h ∣ levelFamLatS b₁ b₂ w B q) → IsUnit h := by
    intro h hh
    refine cubGcdOne b₁ b₂ w hw B hBhom hBne hnolin ?_ hℓ' h ?_
    · rintro ⟨h1, h2⟩
      rcases hnd with h | h
      · exact h (hb1def ▸ h1)
      · exact h (hb2def ▸ h2)
    · intro i hi j hj hij
      have hq : h ∣ levelFamLatS b₁ b₂ w B
          ⟨(⟨i, Finset.mem_range.mp hi⟩, ⟨j, Finset.mem_range.mp hj⟩), by simpa using hij⟩ :=
        hh _
      simpa [levelFamLatS] using hq
  obtain ⟨hfinS, hbndS⟩ := Work.Q44Geom.planeBoundFin Bnd hBnd
    {q : Fin 3 × Fin 3 // (q.1 : ℕ) + (q.2 : ℕ) ≤ 2} (levelFamLatS b₁ b₂ w B) hdeg hgcd
  -- every plane of the set determines a direction of `S`
  have hmaps : ∀ P ∈ Work.HP.MDEstimates.CubPlaneSet B x y, ∃ L ∈
      {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
        ∀ z ∈ L, ∀ q, MvPolynomial.eval z (levelFamLatS b₁ b₂ w B q) = 0},
      P = Submodule.span ℚ
        ({b₁, b₂} ∪ Set.range (fun p : L => Work.Q44Geom.toV w (p : Fin 3 → ℚ))) := by
    intro P hP
    obtain ⟨hr, hb1', hb2', hvanish⟩ := hP
    have hb1'' : b₁ ∈ P := hb1'
    have hb2'' : b₂ ∈ P := hb2'
    obtain ⟨L, hL⟩ := Work.HP.MDEstimates.cubPlaneDirection b₁ b₂ w hw hwspan B hBhom hℓ'
      P hb1'' hb2'' hr hvanish
    refine ⟨L, ⟨hL.1, ?_⟩, hL.2.1⟩
    intro z hz q
    have hres := hL.2.2 z hz (q.1.1 : ℕ) (Finset.mem_range.mpr q.1.1.isLt)
      (q.1.2 : ℕ) (Finset.mem_range.mpr q.1.2.isLt) (by simpa using q.2)
    simpa [levelFamLatS] using hres
  classical
  set S : Set (Submodule ℚ (Fin 3 → ℚ)) :=
    {L | Module.finrank ℚ L = 1 ∧ ∀ z ∈ L,
      ∀ q, MvPolynomial.eval z (levelFamLatS b₁ b₂ w B q) = 0} with hSdef
  have hSfin : S.Finite := by rw [hSdef]; exact hfinS
  have hSbnd : S.ncard ≤ Bnd := by rw [hSdef]; exact hbndS
  let fL : Submodule ℚ (Fin 5 → ℚ) → Submodule ℚ (Fin 3 → ℚ) :=
    fun P => if h : P ∈ Work.HP.MDEstimates.CubPlaneSet B x y then
      Classical.choose (hmaps P h) else ⊥
  have hfL : ∀ P (hP : P ∈ Work.HP.MDEstimates.CubPlaneSet B x y), fL P ∈ S ∧
      P = Submodule.span ℚ
        ({b₁, b₂} ∪ Set.range (fun p : fL P => Work.Q44Geom.toV w (p : Fin 3 → ℚ))) := by
    intro P hP
    have hval : fL P = Classical.choose (hmaps P hP) := by
      simp only [fL]
      rw [dif_pos hP]
    rw [hval]
    exact Classical.choose_spec (hmaps P hP)
  have hinj : Set.InjOn fL (Work.HP.MDEstimates.CubPlaneSet B x y) := by
    intro P hP Q hQ heq
    rw [(hfL P hP).2, (hfL Q hQ).2, heq]
  have hsub : Work.HP.MDEstimates.CubPlaneSet B x y ⊆ fL ⁻¹' S :=
    fun P hP => (hfL P hP).1
  refine ⟨?_, ?_⟩
  · exact (hSfin.subset (Set.image_subset_iff.mpr hsub)).of_finite_image hinj
  · have hbd : (Work.HP.MDEstimates.CubPlaneSet B x y).ncard ≤ Bnd := by
      calc (Work.HP.MDEstimates.CubPlaneSet B x y).ncard
          ≤ (fL '' Work.HP.MDEstimates.CubPlaneSet B x y).ncard :=
            hinj.ncard_image.symm.le
        _ ≤ S.ncard := Set.ncard_le_ncard (Set.image_subset_iff.mpr hsub) hSfin
        _ ≤ Bnd := hSbnd
    have h2 : ((Work.HP.MDEstimates.CubPlaneSet B x y).ncard : ℝ) ≤ (Bnd : ℝ) := by
      exact_mod_cast hbd
    linarith

/-! ## The good members of the cubic counting set -/

/-- The number of good members of the cubic counting set is `≪ (s 0 * s 1 * s 2)^3`. -/
theorem cubGoodCountMain : ∃ C : ℝ, 0 < C ∧ ∀ (B : MvPolynomial (Fin 5) ℚ),
    B.IsHomogeneous 3 → B ≠ 0 →
    (∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) →
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
      (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ C * (s 0 * s 1 * s 2) ^ 3 := by
  obtain ⟨K, hKpos, hK⟩ := cubPlaneBoundMain
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.Q44Geom.zero_count
  refine ⟨K * (Cz * Cz) + 1, by positivity, ?_⟩
  intro B hB hB0 hnolin s hs0 hs01 hs12
  classical
  have htd : B.totalDegree ≤ 4 := le_trans hB.totalDegree_le (by norm_num)
  set P : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) := Work.HP.MDEstimates.CubPairs B s with hPdef
  have hPfin : P.Finite := Work.HP.MDEstimates.cubPairs_finite
  have hGfin : ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
      Set (Submodule ℤ (Fin 5 → ℤ))).Finite := Work.HP.MDEstimates.CubGood_finite
  have hfib : ∀ p ∈ P,
      (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L ∧
        Work.HP.MDEstimates.cubPair B s L = p} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ K := by
    intro p hp
    by_cases hne : ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L ∧
        Work.HP.MDEstimates.cubPair B s L = p} : Set (Submodule ℤ (Fin 5 → ℤ))).Nonempty
    · obtain ⟨L₀, hL₀⟩ := hne
      rw [Set.mem_setOf_eq] at hL₀
      obtain ⟨hL₀good, hL₀pair⟩ := hL₀
      have hspec := Work.HP.MDEstimates.cubPair_spec hL₀good.1
      have hp1 : p.1 = (Work.HP.MDEstimates.cubPair B s L₀).1 := by rw [← hL₀pair]
      have hp2 : p.2 = (Work.HP.MDEstimates.cubPair B s L₀).2 := by rw [← hL₀pair]
      have hgood' : Work.Q44Geom.toRatLM p.1 ∉ Work.Q44Geom.invSub B ∨
          Work.Q44Geom.toRatLM p.2 ∉ Work.Q44Geom.invSub B := by
        rcases hL₀good.2 with h | h
        · exact Or.inl (by rw [hp1]; exact h)
        · exact Or.inr (by rw [hp2]; exact h)
      have hpB1 : MvPolynomial.eval (Work.Q44Geom.toRatLM p.1) B = 0 := by
        rw [hp1]
        exact hL₀good.1.2.2.2 _ hspec.1
      have hpB2 : MvPolynomial.eval (Work.Q44Geom.toRatLM p.2) B = 0 := by
        rw [hp2]
        exact hL₀good.1.2.2.2 _ hspec.2.1
      have hspan : ∀ a c : ℚ,
          MvPolynomial.eval (a • Work.Q44Geom.toRatLM p.1 + c • Work.Q44Geom.toRatLM p.2)
            B = 0 := by
        intro a c
        have hmem : a • Work.Q44Geom.toRatLM p.1 + c • Work.Q44Geom.toRatLM p.2
            ∈ Work.Q44Geom.ratSpan L₀ := by
          refine (Work.Q44Geom.ratSpan L₀).add_mem ?_ ?_
          · rw [hp1]
            exact (Work.Q44Geom.ratSpan L₀).smul_mem a
              (Work.Q44Geom.toRatLM_mem_ratSpan hspec.1)
          · rw [hp2]
            exact (Work.Q44Geom.ratSpan L₀).smul_mem c
              (Work.Q44Geom.toRatLM_mem_ratSpan hspec.2.1)
        exact Work.HP.MDEstimates.vanishRatSpanCub hB hL₀good.1.2.2.2 _ hmem
      have hp1ne : p.1 ≠ 0 := by
        rw [hp1]
        exact Work.HP.MDEstimates.pair_fst_ne_zero hspec.2.2.1
      have hp2ne : p.2 ≠ 0 := by
        rw [hp2]
        exact Work.HP.MDEstimates.pair_snd_ne_zero hspec.2.2.1
      have hbind : LinearIndependent ℚ
          ![Work.Q44Geom.toRatLM p.1, Work.Q44Geom.toRatLM p.2] := by
        rw [hp1, hp2]
        exact Work.HP.MDEstimates.linIndep_rat_pair hspec.2.2.1
      have hbound := hK B hB hB0 hnolin p.1 p.2 hp1ne hp2ne hbind hpB1 hpB2 hspan hgood'
      have hT : ∀ L ∈ ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L ∧
          Work.HP.MDEstimates.cubPair B s L = p} : Set (Submodule ℤ (Fin 5 → ℤ))),
          L ∈ Work.HP.MDEstimates.CubLatSet B s ∧
            (Work.HP.MDEstimates.cubPair B s L).1 = p.1 ∧
            (Work.HP.MDEstimates.cubPair B s L).2 = p.2 := by
        intro L hL
        rw [Set.mem_setOf_eq] at hL
        exact ⟨hL.1.1, by rw [hL.2], by rw [hL.2]⟩
      calc (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L ∧
            Work.HP.MDEstimates.cubPair B s L = p} :
            Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
          ≤ ((Work.HP.MDEstimates.CubPlaneSet B p.1 p.2).ncard : ℝ) := by
            exact_mod_cast Work.HP.MDEstimates.ncard_le_cubPlaneSet hB _ hT hbound.1
        _ ≤ K := hbound.2
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty, Nat.cast_zero]
      positivity
  have hstep : (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
      Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ (P.ncard : ℝ) * K := by
    rw [Set.ncard_eq_toFinset_card _ hGfin]
    have hsum := Finset.card_eq_sum_card_fiberwise (s := hGfin.toFinset) (t := hPfin.toFinset)
      (f := fun L => Work.HP.MDEstimates.cubPair B s L) (fun L hL => by
        rw [Finset.mem_coe] at hL
        rw [Finset.mem_coe, hPfin.mem_toFinset]
        have hspec := Work.HP.MDEstimates.cubPair_spec (hGfin.mem_toFinset.mp hL).1
        exact ⟨hspec.2.2.2.1, hspec.2.2.2.2,
          (hGfin.mem_toFinset.mp hL).1.2.2.2 _ hspec.1,
          (hGfin.mem_toFinset.mp hL).1.2.2.2 _ hspec.2.1⟩)
    rw [hsum]
    push_cast
    calc (∑ p ∈ hPfin.toFinset,
          (((hGfin.toFinset.filter
            (fun L => Work.HP.MDEstimates.cubPair B s L = p)).card : ℕ) : ℝ))
        ≤ ∑ p ∈ hPfin.toFinset, K := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp' : p ∈ P := hPfin.mem_toFinset.mp hp
          have h1 : (((hGfin.toFinset.filter
              (fun L => Work.HP.MDEstimates.cubPair B s L = p)).card : ℕ) : ℝ)
              ≤ (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L ∧
                Work.HP.MDEstimates.cubPair B s L = p} :
                Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
            have hsub : ((hGfin.toFinset.filter
                (fun L => Work.HP.MDEstimates.cubPair B s L = p)) :
                Set (Submodule ℤ (Fin 5 → ℤ))) ⊆
                {L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L ∧
                  Work.HP.MDEstimates.cubPair B s L = p} := by
              intro L hL
              rw [Finset.mem_coe, Finset.mem_filter] at hL
              exact ⟨hGfin.mem_toFinset.mp hL.1, hL.2⟩
            have h2 := Set.ncard_le_ncard hsub (hGfin.subset (fun L hL => hL.1))
            rw [Set.ncard_coe_finset] at h2
            exact_mod_cast h2
          exact le_trans h1 (hfib p hp')
      _ = (hPfin.toFinset.card : ℝ) * K := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (P.ncard : ℝ) * K := by rw [Set.ncard_eq_toFinset_card P hPfin]
  have hPcard : (P.ncard : ℝ) ≤ (Cz * s 0 ^ 4) * (Cz * s 1 ^ 4) := by
    have hsub : P ⊆ ({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 0 ∧
          MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}) ×ˢ
        ({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 1 ∧
          MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}) := by
      intro p hp
      exact ⟨⟨hp.1, hp.2.2.1⟩, ⟨hp.2.1, hp.2.2.2⟩⟩
    have hfinA : ({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 0 ∧
        MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0} :
        Set (Fin 5 → ℤ)).Finite :=
      (Work.HP.MDBasic.finite_eNorm_le (s 0)).subset fun v hv => hv.1
    have hfinB : ({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 1 ∧
        MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0} :
        Set (Fin 5 → ℤ)).Finite :=
      (Work.HP.MDBasic.finite_eNorm_le (s 1)).subset fun v hv => hv.1
    have h1 := hCz B hB0 htd (s 0) hs0
    have h2 := hCz B hB0 htd (s 1) (le_trans hs0 hs01)
    have hcast : ((({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 0 ∧
          MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}) ×ˢ
        ({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 1 ∧
          MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}) :
        Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ)
        = (({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 0 ∧
            MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}).ncard : ℝ) *
          (({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 1 ∧
            MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}).ncard : ℝ) := by
      rw [Set.ncard_prod, Nat.cast_mul]
    calc (P.ncard : ℝ)
        ≤ ((({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 0 ∧
            MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}) ×ˢ
          ({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 1 ∧
            MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}) :
          Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hsub (hfinA.prod hfinB)
      _ = (({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 0 ∧
            MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}).ncard : ℝ) *
          (({v : Fin 5 → ℤ | Work.HP.eNorm v ≤ s 1 ∧
            MvPolynomial.eval (Work.Q44Geom.toRatLM v) B = 0}).ncard : ℝ) := hcast
      _ ≤ (Cz * s 0 ^ 4) * (Cz * s 1 ^ 4) :=
          mul_le_mul h1 h2 (by exact Nat.cast_nonneg _)
            (mul_nonneg hCzpos.le (pow_nonneg (le_trans zero_le_one hs0) 4))
  have hs0n : (0 : ℝ) ≤ s 0 := le_trans zero_le_one hs0
  have hs1n : (0 : ℝ) ≤ s 1 := le_trans zero_le_one (le_trans hs0 hs01)
  have hs2n : (0 : ℝ) ≤ s 2 := le_trans zero_le_one (le_trans (le_trans hs0 hs01) hs12)
  have hX0 : (0 : ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by positivity
  have hX1 : (1 : ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
    have h1 : (1 : ℝ) ≤ s 1 := le_trans hs0 hs01
    have h2 : (1 : ℝ) ≤ s 2 := le_trans h1 hs12
    have h01 : (1 : ℝ) ≤ s 0 * s 1 := by
      have h := mul_le_mul hs0 h1 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (0 : ℝ) ≤ s 0)
      simpa using h
    have h4 : (1 : ℝ) ≤ s 0 * s 1 * s 2 := by
      have h := mul_le_mul h01 h2 (by norm_num : (0 : ℝ) ≤ 1)
        (by nlinarith [hs0, h1] : (0 : ℝ) ≤ s 0 * s 1)
      simpa using h
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (s 0 * s 1 * s 2) ^ 3 := pow_le_pow_left₀ (by norm_num) h4 3
  calc (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ (P.ncard : ℝ) * K := hstep
    _ ≤ ((Cz * s 0 ^ 4) * (Cz * s 1 ^ 4)) * K :=
        mul_le_mul_of_nonneg_right hPcard hKpos.le
    _ = (K * (Cz * Cz)) * (s 0 ^ 4 * s 1 ^ 4) := by ring
    _ ≤ (K * (Cz * Cz)) * (s 0 * s 1 * s 2) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_four_le_latS s hs0 hs01 hs12) (by positivity)
    _ ≤ (K * (Cz * Cz) + 1) * (s 0 * s 1 * s 2) ^ 3 := by
        have : (0 : ℝ) ≤ K * (Cz * Cz) := by positivity
        nlinarith [hX0, hX1]

/-! ## The main count -/

theorem latS_cub_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : MvPolynomial (Fin 5) ℚ), B.IsHomogeneous 3 → B ≠ 0 →
      (∀ ℓ : MvPolynomial (Fin 5) ℚ, ℓ.IsHomogeneous 1 → ℓ ∣ B → False) →
      ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
        (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
           (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
           (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0)} :
          Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
          ≤ C * (s 0 * s 1 * s 2) ^ 3 := by
  obtain ⟨Cg, hCgpos, hCg⟩ := cubGoodCountMain
  obtain ⟨Cb, hCbpos, hCb⟩ := Work.HP.MDEstimates.cubBadCount
  refine ⟨Cb + Cg + 1, by positivity, ?_⟩
  intro B hB hB0 hnolin s hs0 hs01 hs12
  have hs0n : (0 : ℝ) ≤ s 0 := le_trans zero_le_one hs0
  have hs1n : (0 : ℝ) ≤ s 1 := le_trans zero_le_one (le_trans hs0 hs01)
  have hs2n : (0 : ℝ) ≤ s 2 := le_trans zero_le_one (le_trans (le_trans hs0 hs01) hs12)
  have hX0 : (0 : ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by positivity
  have hX1 : (1 : ℝ) ≤ (s 0 * s 1 * s 2) ^ 3 := by
    have h1 : (1 : ℝ) ≤ s 1 := le_trans hs0 hs01
    have h2 : (1 : ℝ) ≤ s 2 := le_trans h1 hs12
    have h01 : (1 : ℝ) ≤ s 0 * s 1 := by
      have h := mul_le_mul hs0 h1 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (0 : ℝ) ≤ s 0)
      simpa using h
    have h4 : (1 : ℝ) ≤ s 0 * s 1 * s 2 := by
      have h := mul_le_mul h01 h2 (by norm_num : (0 : ℝ) ≤ 1)
        (by nlinarith [hs0, h1] : (0 : ℝ) ≤ s 0 * s 1)
      simpa using h
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (s 0 * s 1 * s 2) ^ 3 := pow_le_pow_left₀ (by norm_num) h4 3
  have hG : (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
      Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ Cg * (s 0 * s 1 * s 2) ^ 3 :=
    hCg B hB hB0 hnolin s hs0 hs01 hs12
  have hBad : (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
      Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ Cb * (s 0 * s 1 * s 2) ^ 3 + 1 := by
    have hfin3 : Module.finrank ℚ (Work.Q44Geom.invSub B) ≤ 3 :=
      Work.HP.MDEstimates.cubInv_finrank_le B hB hB0 hnolin
    have hWrk : Work.HP.rk (Work.Q44Geom.latW B) ≤ 3 :=
      le_trans (Work.Q44Geom.latW_rank_le B) hfin3
    by_cases h2 : Work.HP.rk (Work.Q44Geom.latW B) = 2
    · have hle2 : (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
          (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0) ∧
          Work.Q44Geom.latW B ≤ L} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤
          Cb * (s 0 * s 1 * s 2) ^ 3 := hCb B hB hB0 hnolin h2 s hs0 hs01 hs12
      have hsub : ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
          Set (Submodule ℤ (Fin 5 → ℤ))) ⊆
          {L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
            (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
            (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0) ∧
            Work.Q44Geom.latW B ≤ L} :=
        fun L hL =>
          ⟨hL.1.1, hL.1.2.1, hL.1.2.2.1, hL.1.2.2.2,
            Work.HP.MDEstimates.bad_contains_latW h2 hL⟩
      have hfin : ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
            (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
            (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0) ∧
            Work.Q44Geom.latW B ≤ L} : Set (Submodule ℤ (Fin 5 → ℤ))).Finite :=
        Work.HP.MDEstimates.CubLatSet_finite.subset
          (fun L hL => ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1⟩)
      have h1 : (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
          Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ Cb * (s 0 * s 1 * s 2) ^ 3 :=
        le_trans (by exact_mod_cast Set.ncard_le_ncard hsub hfin) hle2
      linarith [mul_nonneg hCbpos.le hX0]
    · by_cases h3 : Work.HP.rk (Work.Q44Geom.latW B) = 3
      · have hf3 : Module.finrank ℚ (Work.Q44Geom.invSub B) = 3 := by
          refine le_antisymm hfin3 ?_
          have hA : Module.finrank ℚ
              (Work.Q44Geom.ratSpan (Work.Q44Geom.latW B)) = 3 := by
            rw [Work.Q44Geom.ratSpan_finrank_general, h3]
          rw [← hA]
          exact Submodule.finrank_mono (Work.Q44Geom.ratSpan_latW_le B)
        have hsub : ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
            Set (Submodule ℤ (Fin 5 → ℤ))) ⊆ ({Work.Q44Geom.latW B} : Set _) := by
          intro L hL
          rw [Set.mem_singleton_iff]
          obtain ⟨hx, hy, hrk2⟩ := Work.HP.MDEstimates.bad_pair_mem hL
          have hne2 : Work.HP.rk (L ⊓ Work.Q44Geom.latW B) ≠ 2 :=
            cubW3NoRk2 B hB hB0 hnolin hf3 L hL.1.1 hL.1.2.1 hL.1.2.2.2
          have hle3 : Work.HP.rk (L ⊓ Work.Q44Geom.latW B) ≤ 3 := by
            calc Work.HP.rk (L ⊓ Work.Q44Geom.latW B)
                = Module.finrank ℤ ↥(L ⊓ Work.Q44Geom.latW B) := rfl
              _ ≤ Module.finrank ℤ ↥L := Submodule.finrank_mono inf_le_left
              _ = Work.HP.rk L := rfl
              _ = 3 := hL.1.2.1
          have hrk3 : Work.HP.rk (L ⊓ Work.Q44Geom.latW B) = 3 := by omega
          have hprim : Work.HP.IsPrimLat (L ⊓ Work.Q44Geom.latW B) :=
            Work.Q44Geom.isPrimLat_inf hL.1.1 (Work.Q44Geom.isPrimLat_latW B)
          have hspan : Work.Q44Geom.ratSpan (L ⊓ Work.Q44Geom.latW B) =
              Work.Q44Geom.ratSpan L := by
            refine Submodule.eq_of_le_of_finrank_eq (Work.Q44Geom.ratSpan_mono inf_le_left) ?_
            rw [Work.Q44Geom.ratSpan_finrank_general, Work.Q44Geom.ratSpan_finrank_general,
              hrk3, hL.1.2.1]
          have heq : L ⊓ Work.Q44Geom.latW B = L :=
            Work.Q44Geom.ratSpan_injective_of_isPrimLat hprim hL.1.1 hspan
          have hLW : L ≤ Work.Q44Geom.latW B := by
            rw [← heq]
            exact inf_le_right
          exact Work.Q44Geom.ratSpan_injective_of_isPrimLat hL.1.1
            (Work.Q44Geom.isPrimLat_latW B) (by
              refine Submodule.eq_of_le_of_finrank_eq (Work.Q44Geom.ratSpan_mono hLW) ?_
              rw [Work.Q44Geom.ratSpan_finrank_general, Work.Q44Geom.ratSpan_finrank_general,
                hL.1.2.1, h3])
        have h1 : (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
            Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) ≤ 1 := by
          have h2' := Set.ncard_le_ncard hsub (Set.finite_singleton (Work.Q44Geom.latW B))
          rw [Set.ncard_singleton] at h2'
          exact_mod_cast h2'
        linarith [h1, mul_nonneg hCbpos.le hX0]
      · have hempty : ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
            Set (Submodule ℤ (Fin 5 → ℤ))) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro L hL
          obtain ⟨-, -, hrk2⟩ := Work.HP.MDEstimates.bad_pair_mem hL
          have hle : Work.HP.rk (L ⊓ Work.Q44Geom.latW B) ≤
              Work.HP.rk (Work.Q44Geom.latW B) := Submodule.finrank_mono inf_le_right
          omega
        rw [hempty, Set.ncard_empty, Nat.cast_zero]
        linarith [mul_nonneg hCbpos.le hX0]
  have hunion : Work.HP.MDEstimates.CubLatSet B s ⊆
      ({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
        Set (Submodule ℤ (Fin 5 → ℤ))) ∪
      {L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} := by
    intro L hL
    by_cases h : (Work.Q44Geom.toRatLM (Work.HP.MDEstimates.cubPair B s L).1 ∉
        Work.Q44Geom.invSub B ∨
        Work.Q44Geom.toRatLM (Work.HP.MDEstimates.cubPair B s L).2 ∉ Work.Q44Geom.invSub B)
    · exact Or.inl ⟨hL, h⟩
    · exact Or.inr ⟨hL, h⟩
  have htot : ((Work.HP.MDEstimates.CubLatSet B s).ncard : ℝ) ≤
      (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) +
      (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
        Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
    calc ((Work.HP.MDEstimates.CubLatSet B s).ncard : ℝ)
        ≤ ((({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubGood B s L} :
            Set (Submodule ℤ (Fin 5 → ℤ))) ∪
            {L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.MDEstimates.CubBad B s L} :
            Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hunion
            (Work.HP.MDEstimates.CubGood_finite.union Work.HP.MDEstimates.CubBad_finite)
      _ ≤ _ := by exact_mod_cast Set.ncard_union_le _ _
  have hmain : ((Work.HP.MDEstimates.CubLatSet B s).ncard : ℝ) ≤
      Cg * (s 0 * s 1 * s 2) ^ 3 + (Cb * (s 0 * s 1 * s 2) ^ 3 + 1) := by linarith
  have hfinal : Cg * (s 0 * s 1 * s 2) ^ 3 + (Cb * (s 0 * s 1 * s 2) ^ 3 + 1) ≤
      (Cb + Cg + 1) * (s 0 * s 1 * s 2) ^ 3 := by nlinarith [hX1]
  exact le_trans hmain hfinal

end Work.HP.Q44Main
