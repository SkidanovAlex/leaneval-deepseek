import Submission.EFL.S12Step1
import Submission.EFL.S12Step10
import Submission.EFL.Nibble
import Submission.EFL.S12Step9Pack
import Submission.EFL.OptCol

import Submission.EFL.NibbleFixed
/-!
# §12: the assembly of the proof of Theorem 1.1

This module wires together the steps of §12 of Kang--Kelly--Kühn--Methuku--Osthus,
*A proof of the Erdős--Faber--Lovász conjecture*.

Everything is parametrised by the numerical hierarchy of the paper; the module
provides (i) the passage from the Step-4 output to the Step-5/6/7 data, (ii) the
definition and analysis of `𝓜_prev`, `G_final` and `𝓗_final`, (iii) the degree
bounds UC1--UC4 and (iv) the three cases of the final step.

The deep inputs of the proof (Kahn, Molloy--Reed, GKO, the nibble and the
leftover lemma) enter as hypotheses.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## Step 4 in the case `C_diff = ∅` -/

/-- **§12, Step 4, trivial case.**  When there are no difficult colours
(`C_diff = ∅`, which is the case for Type B), Step 4 produces nothing new:
`Mdiff = ∅`, `R₁ = R_abs` and `S₁ = S`. -/
theorem isS12Step4_of_Cdiff_empty {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S : Set (Fin n)} {Cdiff : Finset (Fin n)}
    {R_abs : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))} {ρ_abs γ ξ : ℝ}
    (hCdiff : Cdiff = ∅)
    (habs : IsAbsorber (incidentTwo 𝓗 U) R_abs 𝓥 ρ_abs ξ ξ)
    (hγξ : ξ ≤ 3 * γ / 2) :
    IsS12Step4 𝓗 φ U S Cdiff R_abs R_abs S (fun _ : Fin n => (∅ : Set 𝓗)) 𝓥 ρ_abs γ ξ := by
  have hfam : famUnionIdx (fun _ : Fin n => (∅ : Set 𝓗)) = ∅ := by
    ext e
    rw [mem_famUnionIdx]
    constructor
    · rintro ⟨i, hi⟩
      rw [mem_famOf] at hi
      obtain ⟨e', he', -⟩ := hi
      exact he'
    · intro he
      exact absurd he (by simp)
  have hX : (⋃ c ∈ (Cdiff : Set (Fin n)),
      (Vdeg 𝓗 (n - 2) \ matchVert ((fun _ => (∅ : Set 𝓗)) c))) = ∅ := by
    rw [hCdiff]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, subset_rfl, ?_, ?_⟩
  · intro c hc; rfl
  · intro c hc; rw [hCdiff] at hc; exact absurd hc (Finset.notMem_empty c)
  · intro c hc; rw [hCdiff] at hc; exact absurd hc (Finset.notMem_empty c)
  · intro c; exact isMatching_empty 𝓗
  · intro c hc; rw [hCdiff] at hc; exact absurd hc (Finset.notMem_empty c)
  · intro c hc; rw [hCdiff] at hc; exact absurd hc (Finset.notMem_empty c)
  · rw [hfam, Set.sdiff_empty]
  · rw [hX, Set.sdiff_empty]
  · exact IsAbsorber.mono_gamma habs hγξ
  · simp

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The numerical margins of §12 -/

/-- The numerical hypotheses of the §12 assembly: the paper's hierarchy
`1/n ≪ ξ ≪ 1/r₁ ≪ β ≪ κ ≪ γ ≪ ε ≪ ρ ≪ 1` in the explicit form used by the
individual steps. -/
structure S12Margins (n : ℕ) (r₁ r₀ : ℕ) (β γ ρ ρ_abs ξ ε κ : ℝ) : Prop where
  hmHuge : HugeMargins n ρ_abs ε (3 * γ / 2) κ ξ
  hmDeg : DegreeMargins n ρ ξ ε (β / 2) r₁
  hβ0 : 0 < β
  hγ0 : 0 ≤ γ
  hε0 : 0 ≤ ε
  hξ0 : 0 ≤ ξ
  hn1 : 1 ≤ n
  hnpos : 0 < n
  hn4 : 4 ≤ n
  hr₁2 : 2 ≤ r₁
  hr₀2 : 2 ≤ r₀
  hr₁r₀ : r₁ < r₀
  hξγ2 : 10 * ξ + 3 * γ / 2 ≤ 2 * γ
  hγε : γ ≤ 2 * ε
  hεn : 2 ≤ ε * (n : ℝ)
  hk2 : 32 / β ^ 2 ≤ γ * (n : ℝ) / 2
  hβn : 8 ≤ β * (n : ℝ)
  hr₁β : (r₁ : ℝ) < β * (n : ℝ) / 4
  hS₂num : (Dparam n ρ : ℝ) + 3 * γ * (n : ℝ) / 2 + 5 + 4 * ε * (n : ℝ) ≤
    (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ)
  hnum1 : 2 / 3 * β * (n : ℝ) + 2 ≤ 2 * β * (Dparam n ρ : ℝ)
  hnD : (n : ℝ) ≤ 2 * (Dparam n ρ : ℝ)
  hEP2num : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ 2 * β * (Dparam n ρ : ℝ)
  hL1 : (10 * Real.sqrt γ) * ((Dparam n ρ : ℕ) : ℝ) / 2 ≤
    (D'param (Dparam n ρ) γ : ℕ)
  hβγ : β ≤ 5 * Real.sqrt γ
  hL3 : 4 * γ ≤ 100 * Real.sqrt γ
  hL4ov : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ γ * ((Dparam n ρ : ℕ) : ℝ)
  hL5 : 10 * Real.sqrt γ < 3 * ε
  /-- the asymptotic side conditions of the Nibble Lemma `lem:nibble2`, in the
  *corrected* (session 4) form `NibbleMarginsStrong`: the seeded `NibbleMargins`
  is provably too weak for the paper's §7 assembly (see the docstring of
  `NibbleStatement` in `Submission/EFL/Nibble.lean`) -/
  hnib : NibbleMarginsStrong n ((Dparam n ρ : ℕ) : ℝ) r₁ (2 * β) (2 * γ) ε ρ_abs ξ

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Step 5, in the form needed by both Type A and Type B -/

/-- **§12, Step 5, generic form.**  Same as `s12_step5_pack`, but with the size
bounds on the huge/medium colour classes supplied directly (rather than derived
from `φ.SingletonClassesForHuge` in the Type A case). -/
theorem s12_step5_pack_gen {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℝ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U S S₁ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_abs R₁ : Hypergraph (Fin n)} {Mdiff : Fin n → Set 𝓗}
    (hlin : 𝓗.IsLinear)
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hm : HugeMargins n ρ_abs ε (3 * γ / 2) κ ξ)
    (hU : U = Vplus 𝓗 (1 - ε))
    (hstep4 : IsS12Step4 𝓗 φ U S Cdiff R_abs R₁ S₁ Mdiff (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs γ ξ)
    (hR_abs_pow2 : R_abs ⊆ 𝓗.pow2) (hSsubU : S ⊆ U)
    {ζ : ℝ} (hR₁_small : IsAbsorber (incidentTwo 𝓗 U) R₁ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs ζ ξ)
    (hξγ2 : ζ + 3 * γ / 2 ≤ 2 * γ)
    (hn4 : 4 ≤ n) (hγ0 : 0 ≤ γ) (hε0 : 0 ≤ ε) (hεn : 2 ≤ ε * (n : ℝ))
    (hk2 : 32 / β ^ 2 ≤ γ * (n : ℝ) / 2)
    (hβ : 0 < β) (hβn : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hr₁2 : 2 ≤ r₁) (hr₁β : r₁ < β * (n : ℝ) / 4)
    (hS_big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ (S.ncard : ℝ))
    (hS₂num : (Dparam n ρ : ℝ) + 3 * γ * (n : ℝ) / 2 + 5 + 4 * ε * (n : ℝ) ≤
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ))
    (hbigsize : ∀ c ∈ Chuge,
      ((matchVert (colourFam φ c) ∩ U).ncard : ℝ) ≤ ε * (n : ℝ))
    (hmedsize : ∀ c ∈ Cmed,
      ((matchVert (colourFam φ c)).ncard : ℝ) ≤ (3 * γ / 2) * (n : ℝ)) :
    ∃ (Mhm : Fin n → Set 𝓗) (R₂ : Hypergraph (Fin n)) (S₂ : Set (Fin n)),
      IsS12Step5 (φ := φ) (U := U) (S₁ := S₁) (S₂ := S₂) (r₀ := r₀) (β := β) (γ := γ)
        (ρ := ρ) (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (Chuge := Chuge) (Cmed := Cmed)
        (R₁ := R₁) (R₂ := R₂) (Mhm := Mhm) (𝓥 := (cvFinset φ U : Set (Set (Fin n)))) := by
  classical
  -- ## the raw Step 5
  have hUdeg : ∀ u ∈ U, (1 - ε) * (n : ℝ) ≤ (degAt (incidentTwo 𝓗 U) u : ℝ) := by
    intro u hu
    rw [degAt_incidentTwo_eq 𝓗 hu, hU] at *
    rw [hU] at hu
    exact hu
  have hU𝓥 : U ∈ (cvFinset φ U : Set (Set (Fin n))) := mem_cvFinset_U
  have huniv𝓥 : (Set.univ : Set (Fin n)) ∈ (cvFinset φ U : Set (Set (Fin n))) :=
    mem_cvFinset_univ
  have hbig𝓥 : ∀ c ∈ Chuge ∪ Cmed,
      U ∪ matchVert (colourFam φ c) ∈ (cvFinset φ U : Set (Set (Fin n))) := by
    intro c _
    rw [matchVert_colourFam c]
    exact mem_cvFinset_union c
  have hsmall𝓥 : ∀ c ∈ Chuge ∪ Cmed,
      U \ matchVert (colourFam φ c) ∈ (cvFinset φ U : Set (Set (Fin n))) := by
    intro c _
    rw [matchVert_colourFam c]
    exact mem_cvFinset_sdiff c
  have hnotdiff : ∀ c ∈ Chuge, ¬ IsDifficult U (colourFam φ c) := by
    intro c hc hdiff
    rw [hS12.hChuge_eq] at hc
    obtain ⟨hcs, hcnot⟩ := Finset.mem_sdiff.mp hc
    have hds : IsDifficultSet U (φ.classVertices c) := by
      rw [← matchVert_colourFam c]
      exact isDifficult_iff_difficultSet.mp hdiff
    exact hcnot (Finset.mem_union_right _
      (hS12.hCdiff_full c hcs (fun h => hcnot (Finset.mem_union_left _ h)) hds))
  have hR₁sub2 : R₁ ⊆ 𝓗.pow2 := by
    rw [hstep4.hR₁_eq]
    exact Set.sdiff_subset.trans hR_abs_pow2
  have hNR₁ : ∀ c ∈ Chuge ∪ Cmed, ∀ e ∈ colourFam φ c, (e : Set (Fin n)) ∉ R₁ := by
    intro c _ e he hR1
    have hpow := (mem_pow2.mp (hR₁sub2 hR1)).2
    obtain ⟨hmed, -⟩ := mem_colourFam.mp he
    have hsz := hmed.2
    rw [hpow] at hsz
    norm_num at hsz
    linarith
  have hk : (((Chuge ∪ Cmed).card : ℕ) : ℝ) ≤ (3 * γ / 2) * (n : ℝ) :=
    card_chuge_union_cmed_le hlin hS12 hk2 hβ hβn hn1 hr₁β
  have hB : ((0 : ℕ) : ℝ) ≤ ρ_abs ^ 2 * ((3 * γ / 2) * (n : ℝ)) / 400 := by
    have h1 : (0 : ℝ) ≤ ρ_abs ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (3 * γ / 2) * (n : ℝ) := by
      have h3 := hm.hγ
      have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith
    have h3 : (0 : ℝ) ≤ ρ_abs ^ 2 * ((3 * γ / 2) * (n : ℝ)) := mul_nonneg h1 h2
    linarith
  have hS₁big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      ((3 * γ / 2) + ε) * (n : ℝ) < (S₁.ncard : ℝ) := by
    intro hUbig
    have h1 := hS_big hUbig
    have h2 := hstep4.hS₁_big
    have h3 : (0 : ℝ) ≤ (Dparam n ρ : ℝ) := Nat.cast_nonneg _
    nlinarith [hS₂num, h1, h2, h3]
  obtain ⟨Mhm, hm_supp, hm_ext, hm_add, hm_mat, hm_disj, hm_perf, hm_near, hm_miss⟩ :=
    s12_step5 (n := n) (𝓗 := 𝓗) (r₁ := r₁) (φ := φ) (U := U)
      (ρ_abs := ρ_abs) (ε := ε) (γ := γ) (κ := κ) (ξ := ξ) (B := 0)
      (hm := hm) (hmatch := internalMatchingInput n 0) (hUdeg := hUdeg) (hn4 := hn4)
      (hB := hB) (R₁ := R₁) (S₁ := S₁) (𝓥 := (cvFinset φ U : Set (Set (Fin n))))
      (hR₁sub2 := hR₁sub2) (hSsub := hstep4.hS₁_sub.trans hSsubU) (hSbig := hS₁big)
      (hR₁abs := hstep4.hR₁_abs) (hU𝓥 := hU𝓥) (huniv𝓥 := huniv𝓥) (Chuge := Chuge)
      (Cmed := Cmed) (hbig𝓥 := hbig𝓥) (hsmall𝓥 := hsmall𝓥) (hbigsize := hbigsize)
      (hmedsize := hmedsize) (hnotdiff := hnotdiff) (hNR₁ := hNR₁) (hk := hk)
  -- ## the packaging
  set X : Hypergraph (Fin n) := famUnionFinset Mhm (Chuge ∪ Cmed) with hX
  set R₂ : Hypergraph (Fin n) := R₁ \ X with hR₂
  set Y : Set (Fin n) :=
    ⋃ c ∈ (Chuge ∪ Cmed : Finset (Fin n)), (U \ matchVert (Mhm c)) with hY
  set S₂ : Set (Fin n) := S₁ \ Y with hS₂
  refine ⟨Mhm, R₂, S₂, hm_supp, hm_ext, hm_add, hm_mat, hm_disj, hm_perf, hm_near,
    hm_miss, hR₂, ?_, hS₂, Set.sdiff_subset, ?_⟩
  · -- `(eq:R2abs)`
    have hR₂sub : R₂ ⊆ R₁ := Set.sdiff_subset
    have hΔ : ∀ v : Fin n, (degAt (R₁ \ R₂) v : ℝ) ≤ (3 * γ / 2) * (n : ℝ) := by
      intro v
      have hsub : R₁ \ R₂ ⊆ X := by
        intro e he
        rw [Set.mem_sdiff] at he
        by_contra hXe
        exact he.2 (by rw [hR₂, Set.mem_sdiff]; exact ⟨he.1, hXe⟩)
      have h1 : degAt (R₁ \ R₂) v ≤ degAt X v := degAt_mono hsub v
      have h2 : degAt X v ≤ MultiHypergraph.hdeg X v := degAt_le_hdeg _ v
      have h3 : MultiHypergraph.hdeg X v ≤ (Chuge ∪ Cmed).card := by
        rw [hX]; exact hdeg_famUnionFinset_le_card hm_mat v
      have h4 : (degAt (R₁ \ R₂) v : ℝ) ≤ ((Chuge ∪ Cmed).card : ℝ) := by
        exact_mod_cast le_trans (le_trans h1 h2) h3
      linarith
    have hdel := IsAbsorber.delete (α := 3 * γ / 2) hR₁_small hR₂sub hΔ
    exact IsAbsorber.mono_gamma hdel hξγ2
  · -- `(eq:boundS2)`
    intro hUbig
    have hYle : (Y.ncard : ℝ) ≤ ((Chuge ∪ Cmed).card : ℝ) := by
      have h1 : Y.ncard ≤ ∑ c ∈ (Chuge ∪ Cmed), (U \ matchVert (Mhm c)).ncard := by
        rw [hY]
        exact Commons.Combinatorics.Set.ncard_biUnion_le (Chuge ∪ Cmed) _
          (fun c _ => Set.toFinite _)
      have h2 : ∑ c ∈ (Chuge ∪ Cmed), (U \ matchVert (Mhm c)).ncard ≤
          (Chuge ∪ Cmed).card := by
        calc ∑ c ∈ (Chuge ∪ Cmed), (U \ matchVert (Mhm c)).ncard
            ≤ ∑ _c ∈ (Chuge ∪ Cmed), 1 :=
              Finset.sum_le_sum (fun c hc => (hm_near hUbig).1 c hc)
          _ = (Chuge ∪ Cmed).card := by simp
      exact_mod_cast le_trans h1 h2
    have hsplit : S₁ = S₂ ∪ (S₁ ∩ Y) := by
      rw [hS₂]
      ext x
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    have hdisj : Disjoint S₂ (S₁ ∩ Y) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hxY⟩ ⟨-, hxY'⟩
      exact hxY hxY'
    have hncard : (S₁.ncard : ℝ) ≤ (S₂.ncard : ℝ) + (Y.ncard : ℝ) := by
      have h1 : S₁.ncard = S₂.ncard + (S₁ ∩ Y).ncard := by
        have h1' : S₁.ncard = (S₂ ∪ (S₁ ∩ Y)).ncard := by
          conv_lhs => rw [hsplit]
        rw [h1', Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
      have h2 : ((S₁ ∩ Y).ncard : ℝ) ≤ (Y.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
      have h3 : (S₁.ncard : ℝ) = (S₂.ncard : ℝ) + ((S₁ ∩ Y).ncard : ℝ) := by
        rw [h1]; push_cast; ring
      linarith
    have h1 := hS_big hUbig
    have h2 := hstep4.hS₁_big
    have h3 : (S₁.ncard : ℝ) ≤ (S₂.ncard : ℝ) + (3 * γ / 2) * (n : ℝ) := by
      linarith [hk]
    linarith

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Steps 6 and 7 -/

/-- **§12, Steps 6 and 7.**  From the Step-5 output (the matchings `𝓜_hm` and
the absorber `R₂`), the nibble lemma and the leftover lemma produce the
matchings `𝓜_main`, `𝓜_buff`, the absorber `R₃ = R₂ ∖ ⋃𝓜_main` and the defect
set `S₃`. -/
theorem s12_steps67 {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {β γ ρ ρ_abs ξ ε κ : ℝ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)} {U S₁ S₂ : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    {R_res R_abs R₁ R₂ : Hypergraph (Fin n)} {Mdiff Mhm : Fin n → Set 𝓗}
    (hlin : 𝓗.IsLinear) (hbig : ∀ f ∈ 𝓗, 2 ≤ edgeSize f)
    (hNib : NibblePointwise r₁ (2 * β) (2 * γ) ε ρ_abs ξ n)
    (hleft : LeftoverMargins n r₁ γ ρ ρ_abs ε ξ)
    (hS12 : IsS12Colours n 𝓗 (r₁ : ℝ) φ U (r₀ : ℝ) β γ ρ Cmed Cdiff Chuge Clarge Cmain
      Cbuff Cfinal)
    (hvert : ∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
      (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))
    (hres : IsReservoirTypeA1 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∨
      IsReservoirTypeA2 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∨
      (IsReservoirTypeB 𝓗 R_res (cvFinset φ U : Set (Set (Fin n))) ρ ξ ε ∧
        2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ)))
    (hVuniv : (Set.univ : Set (Fin n)) ∈ (cvFinset φ U : Set (Set (Fin n))))
    (hU𝓥 : U ∈ (cvFinset φ U : Set (Set (Fin n))))
    (hU : U = Vplus 𝓗 (1 - ε))
    (hstep4 : IsS12Step4 𝓗 φ U S₁ Cdiff R_abs R₁ S₁ Mdiff
      (cvFinset φ U : Set (Set (Fin n))) ρ_abs γ ξ)
    (hstep5 : IsS12Step5 (φ := φ) (U := U) (S₁ := S₁) (S₂ := S₂) (r₀ := r₀) (β := β)
      (γ := γ) (ρ := ρ) (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (Chuge := Chuge) (Cmed := Cmed)
      (R₁ := R₁) (R₂ := R₂) (Mhm := Mhm) (𝓥 := (cvFinset φ U : Set (Set (Fin n)))))
    (hm : S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ)
    (hRabs_sub : R_abs ⊆ R_res) (hRabs_pow2 : R_abs ⊆ 𝓗.pow2)
    (hS₁subU : S₁ ⊆ U) :
    ∃ (Mmain : Fin n → Set 𝓗) (Mbuff : Fin n → Set 𝓗) (R₃ : Hypergraph (Fin n))
      (S₃ : Set (Fin n)) (N : Fin Cmain.card → Set (Set (Fin n))),
      S12Step6Result 𝓗 r₁ φ U S₂ Cmain Cdiff Mdiff R_res R₂ R_abs
          (cvFinset φ U : Set (Set (Fin n))) β γ ρ ρ_abs ξ ε ∧
      S12Step7Result 𝓗 r₁ φ U S₃ Cbuff R₃
        (𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset Mdiff Cdiff ∪
          (⋃ i : Fin Cmain.card, N i))) ε := by
  classical
  -- ## Step 6
  have hMdiff_empty : ∀ c ∉ Cdiff, Mdiff c = ∅ := hstep4.hMdiff_supp
  have hMdiff_mat : ∀ c, IsMatching 𝓗 (Mdiff c) := hstep4.hMdiff_mat
  have hstep5' := hstep5
  have hR₂abs : IsAbsorber (incidentTwo 𝓗 U) R₂ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs (2 * γ) ξ := hstep5.hR₂_abs
  have hS₂big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (Dparam n ρ : ℝ) + 4 * ε * (n : ℝ) ≤ (S₂.ncard : ℝ) := hstep5.hS₂_big
  have hmDeg := hm.hmDeg
  have hR₂sub : R₂ ⊆ R_res := by
    intro e he
    rw [hstep5.hR₂_eq] at he
    have h2 : e ∈ R₁ := he.1
    rw [hstep4.hR₁_eq] at h2
    exact hRabs_sub h2.1
  have hS₂subU : S₂ ⊆ U := hstep5.hS₂_sub.trans hS₁subU
  obtain ⟨𝓗', 𝓗star, N, Mmain, h6₁, h6₂, h6₃, h6₄, h6₅, h6₆, h6₇, h6₈, h6₉, h6₁₀,
    h6₁₁, h6₁₂, h6₁₃, h6₁₄, h6₁₅, h6₁₆, h6₁₇, h6₁₈, h6₁₉, h6₂₀, h6₂₁, h6₂₂, h6₂₃⟩ :=
    s12_step6 (n := n) (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
      (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε)
      hlin hbig hmDeg hm.hn1 hm.hnpos hm.hr₀2 hNib hm.hnib hS12 hvert hres hVuniv hU𝓥
      hMdiff_empty hMdiff_mat hR₂abs hRabs_sub hRabs_pow2 hS₂subU hR₂sub hU hS₂big hm.hγ0 hm.hγε
      hm.hnum1 hm.hnD hm.hEP2num
  -- ## `𝓗_rem`, `R₃`, `S₃`
  set 𝓗rem : Hypergraph (Fin n) :=
    𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset Mdiff Cdiff ∪
      (⋃ i : Fin Cmain.card, N i)) with h𝓗rem
  set R₃ : Hypergraph (Fin n) := R₂ \ (⋃ i : Fin Cmain.card, N i) with hR₃
  set S₃ : Set (Fin n) := S₂ \ (⋃ i : Fin Cmain.card, (U \ famVert (N i))) with hS₃
  have hR₃eq : R₃ = R₂ \ (⋃ i : Fin Cmain.card, N i) := rfl
  have hR₃abs : IsAbsorber (incidentTwo 𝓗 U) R₃ (cvFinset φ U : Set (Set (Fin n)))
      ρ_abs (4 * γ) ξ := h6₁₈
  have hR₃pow : R₃ ⊆ 𝓗.pow2 := by
    intro e he
    rw [hR₃] at he
    have h1 : e ∈ R₂ := he.1
    rw [hstep5.hR₂_eq] at h1
    have h2 : e ∈ R₁ := h1.1
    rw [hstep4.hR₁_eq] at h2
    exact hRabs_pow2 h2.1
  have hS₃sub : S₃ ⊆ U := by
    intro v hv
    rw [hS₃] at hv
    exact hS₁subU (hstep4.hS₁_sub (hstep5.hS₂_sub hv.1))
  have hS₃big : (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      4 * ε * (n : ℝ) ≤ (S₃.ncard : ℝ) := h6₂₂
  have hremDeg : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗rem w : ℝ) ≤
      2 * γ * ((Cmain.card : ℕ) : ℝ) := h6₁₇
  -- ## Step 7
  have hL1 : (10 * Real.sqrt γ) * ((Cmain.card : ℕ) : ℝ) / 2 ≤ (Cbuff.card : ℝ) := by
    rw [hS12.hCmain_card, hS12.hCbuff_card]
    exact hm.hL1
  have hL4ov : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ γ * ((Cmain.card : ℕ) : ℝ) := by
    rw [hS12.hCmain_card]
    exact hm.hL4ov
  obtain ⟨Mbuff, h7₁, h7₂, h7₃, h7₄, h7₅, h7₆, h7₇, h7₈, h7₉⟩ :=
    s12_step7 (n := n) (𝓗 := 𝓗) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
      (ρ_abs := ρ_abs) (ξ := ξ) (ε := ε) (φ := φ) (U := U) (S₃ := S₃)
      hS12 hvert hlin hbig hleft hm.hnpos hm.hr₀2 hm.hr₁r₀ (Mdiff := Mdiff)
      (R_res := R_res) (R₂ := R₂) (R₃ := R₃) (𝓥 := (cvFinset φ U : Set (Set (Fin n))))
      (Ncm := N) hR₃eq hR₃abs hR₃pow hR₂sub hS₃sub hU hU𝓥 hVuniv hremDeg hm.hγ0 hS₃big
      hL1 hm.hβγ hm.hL3 hL4ov hm.hL5
  exact ⟨Mmain, Mbuff, R₃, S₃, N,
    ⟨𝓗', 𝓗star, N, Mmain, h6₁, h6₂, h6₃, h6₄, h6₅, h6₆, h6₇, h6₈, h6₉, h6₁₀, h6₁₁,
      h6₁₂, h6₁₃, h6₁₄, h6₁₅, h6₁₆, h6₁₇, h6₁₈, h6₁₉, h6₂₀, h6₂₁, h6₂₂, h6₂₃⟩,
    ⟨Mbuff, h7₁, h7₂, h7₃, h7₄, h7₅, h7₆, h7₇, h7₈, h7₉⟩⟩

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

theorem famVert_toFam_eq {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))}
    (hG : G ⊆ 𝓗) (h : ∀ e ∈ G, 2 ≤ e.ncard) :
    famVert G = matchVert (toFam (𝓗 := 𝓗) G) := by
  rw [← famVert_famOf (toFam (𝓗 := 𝓗) G), famOf_toFam_eq hG h]

/-- `𝓜_prev` as a family of matchings of `𝓗` (the family of the paper). -/
def prevFamE {𝓗 : Hypergraph (Fin n)} (MD HM MM MB : Fin n → Set 𝓗)
    (Cdiff Cmain Cbuff : Finset (Fin n)) (c : Fin n) : Set 𝓗 :=
  toFam (prevFam MD HM MM MB Cdiff Cmain Cbuff c)

theorem mem_prevFamE {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)} {c : Fin n} {e : 𝓗} :
    e ∈ prevFamE MD HM MM MB Cdiff Cmain Cbuff c ↔
      (e : Set (Fin n)) ∈ nonsing (prevFam MD HM MM MB Cdiff Cmain Cbuff c) :=
  Iff.rfl

theorem famVert_prevFamE {𝓗 : Hypergraph (Fin n)} (hbig : ∀ e ∈ 𝓗, 2 ≤ e.ncard)
    (MD HM MM MB : Fin n → Set 𝓗) (Cdiff Cmain Cbuff : Finset (Fin n)) (c : Fin n) :
    famVert (prevFam MD HM MM MB Cdiff Cmain Cbuff c) =
      matchVert (prevFamE MD HM MM MB Cdiff Cmain Cbuff c) :=
  famVert_toFam_eq (fun _ he => prevFam_subset_hyp MD HM MM MB Cdiff Cmain Cbuff c he)
    (fun e he => by
      have h := prevFam_subset_hyp MD HM MM MB Cdiff Cmain Cbuff c he
      exact hbig e h)

theorem famOf_prevFamE {𝓗 : Hypergraph (Fin n)} (hbig : ∀ e ∈ 𝓗, 2 ≤ e.ncard)
    (MD HM MM MB : Fin n → Set 𝓗) (Cdiff Cmain Cbuff : Finset (Fin n)) (c : Fin n) :
    famOf (prevFamE MD HM MM MB Cdiff Cmain Cbuff c) =
      prevFam MD HM MM MB Cdiff Cmain Cbuff c :=
  famOf_toFam_eq (fun _ he => prevFam_subset_hyp MD HM MM MB Cdiff Cmain Cbuff c he)
    (fun e he => by
      have h := prevFam_subset_hyp MD HM MM MB Cdiff Cmain Cbuff c he
      exact hbig e h)

theorem isMatching_prevFamE {𝓗 : Hypergraph (Fin n)} {MD HM MM MB : Fin n → Set 𝓗}
    {Cdiff Cmain Cbuff : Finset (Fin n)}
    (hD : ∀ c, IsMatching 𝓗 (MD c)) (hH : ∀ c, IsMatching 𝓗 (HM c))
    (hM : ∀ c, IsMatching 𝓗 (MM c)) (hB : ∀ c, IsMatching 𝓗 (MB c)) (c : Fin n) :
    IsMatching 𝓗 (prevFamE MD HM MM MB Cdiff Cmain Cbuff c) :=
  isMatching_prevFam_toFam hD hH hM hB c

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The final data of §12 (Steps 8 and 9) -/

/-- **The output of §12 Steps 8 and 9** for the fixed data `φ`, `U`, `S₁`,
`C_prev`, `C_final`, `R_res`: the family `𝓜_prev` of matchings, the final
reservoir `R_final`, the final hypergraph `𝓗_final = 𝓗 ∖ ⋃𝓜_prev`, the
decomposition `(eqn:h_final)`, the deficit bound `(eqn:deficit)` and the
degree bounds `UC1`--`UC4` together with the count of vertices of degree
`< |C_final|`. -/
structure S12Out {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (U S₁ : Set (Fin n))
    (Cprev Cfinal : Finset (Fin n)) (R_res : Hypergraph (Fin n))
    (Mprev : Fin n → Set 𝓗) (R_final 𝓗fin : Hypergraph (Fin n)) (ρ ε γ : ℝ) : Prop where
  hsup : ∀ c ∉ Cprev, Mprev c = ∅
  hext : ∀ c ∈ Cprev, colourFam φ c ⊆ Mprev c
  hmat : ∀ c, IsMatching 𝓗 (Mprev c)
  hRfin : R_final = R_res \ famUnionIdx Mprev
  hRfin2 : ∀ e ∈ R_final, e.ncard = 2
  hRfin_sub : R_final ⊆ R_res
  hfin_eq : 𝓗fin = R_final ∪ famUnionFinset (fun c => colourFam φ c) Cfinal
  hdeg_fin : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗fin w : ℝ) =
    (degAt R_final w : ℝ) + ((finalColoursAt φ Cfinal w).card : ℝ)
  hdecomp : ∀ e : 𝓗, (∃ c ∈ Cprev, e ∈ Mprev c) ∨
    ((e : Set (Fin n)) ∈ R_final ∨ ∃ c ∈ Cfinal, e ∈ colourFam φ c)
  hdeficit : ∀ w : Fin n, (degAt (R_res \ R_final) w : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ)
  hUC1 : ∀ w : Fin n, w ∉ U →
    (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ) - ρ * ε * (n : ℝ) / 4
  hUC2 : ∀ w : Fin n, w ∈ U → w ∉ Vn1set 𝓗 →
    (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ) - 1
  hUC3 : ∀ w : Fin n, w ∈ Vn1set 𝓗 →
    (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ)
  hUC4 : ((∀ v : Fin n, v ∈ Vn1set 𝓗 → v ∉ S₁) ∨
      (U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) → ∀ w : Fin n, w ∈ Vn1set 𝓗 →
    (MultiHypergraph.hdeg 𝓗fin w : ℝ) ≤ (Cfinal.card : ℝ) - 1
  hcount : (Cfinal.card : ℝ) ≤
    (({v : Fin n | (MultiHypergraph.hdeg 𝓗fin v : ℝ) < (Cfinal.card : ℝ)}) :
      Set (Fin n)).ncard

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## The degree of the union of the colour classes of `C_final` -/

/-- A colour class is determined by any one of its edges. -/
theorem colourFam_eq_of_mem {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {c c' : Fin n} {e : 𝓗}
    (he : e ∈ colourFam φ c) (he' : e ∈ colourFam φ c') : c = c' := by
  obtain ⟨h1, h2⟩ := mem_colourFam.mp he
  obtain ⟨h1', h2'⟩ := mem_colourFam.mp he'
  rw [mem_colorClass] at h2 h2'
  have hsub : (⟨(e : Set (Fin n)), h1⟩ : ↥(medLarge 𝓗 r₁)) =
      ⟨(e : Set (Fin n)), h1'⟩ := Subtype.ext rfl
  rw [← hsub] at h2'
  exact h2.symm.trans h2'

/-- An edge of the union of the colour classes of `C` determines its colour
uniquely. -/
theorem existsUnique_colour_of_mem_union {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {C : Finset (Fin n)} {e : Set (Fin n)}
    (h : e ∈ famUnionFinset (fun c => colourFam φ c) C) :
    ∃! c : Fin n, c ∈ C ∧ e ∈ famOf (colourFam φ c) := by
  obtain ⟨c, hc, he⟩ := mem_famUnionFinset.mp h
  refine ⟨c, ⟨hc, he⟩, ?_⟩
  rintro c' ⟨hc', he'⟩
  obtain ⟨e₁, he₁, heq₁⟩ := mem_famOf.mp he
  obtain ⟨e₂, he₂, heq₂⟩ := mem_famOf.mp he'
  have heq : e₁ = e₂ := Subtype.ext (heq₁.trans heq₂.symm)
  subst heq
  exact (colourFam_eq_of_mem he₁ he₂).symm

/-- An edge of a colour class containing a vertex is unique. -/
theorem eq_of_mem_famOf_colourFam_of_mem {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {c : Fin n} {e e' : Set (Fin n)} {w : Fin n}
    (he : e ∈ famOf (colourFam φ c)) (he' : e' ∈ famOf (colourFam φ c))
    (hw : w ∈ e) (hw' : w ∈ e') : e = e' := by
  obtain ⟨e₁, he₁, heq₁⟩ := mem_famOf.mp he
  obtain ⟨e₂, he₂, heq₂⟩ := mem_famOf.mp he'
  by_contra hne
  have hne' : e₁ ≠ e₂ := by
    intro h
    exact hne (by rw [← heq₁, h, heq₂])
  have hdisj := isMatching_colourFam c he₁ he₂ hne'
  exact (Set.disjoint_left.mp hdisj) (by rw [heq₁]; exact hw) (by rw [heq₂]; exact hw')

/-- The degree of the union of the colour classes of `C` at `w` is the number
of colours of `C` whose colour class contains `w`. -/
theorem hdeg_famUnionFinset_colourFam {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} (C : Finset (Fin n)) (w : Fin n) :
    MultiHypergraph.hdeg (famUnionFinset (fun c => colourFam φ c) C) w =
      (finalColoursAt φ C w).card := by
  classical
  rw [MultiHypergraph.hdeg]
  -- the two sets
  set S : Set (Set (Fin n)) :=
    ({e ∈ famUnionFinset (fun c => colourFam φ c) C | w ∈ e} : Set (Set (Fin n))) with hS
  set T : Set (Fin n) := ((finalColoursAt φ C w : Finset (Fin n)) : Set (Fin n)) with hT
  have hexA : ∀ e ∈ S, e ∈ famUnionFinset (fun c => colourFam φ c) C ∧ w ∈ e :=
    fun e he => he
  have hTB : ∀ c ∈ T, c ∈ C ∧ w ∈ matchVert (colourFam φ c) := by
    intro c hc
    rwa [hT, finalColoursAt, Finset.mem_coe, Finset.mem_filter] at hc
  have hexB2 : ∀ c ∈ T, ∃ e : Set (Fin n), e ∈ famOf (colourFam φ c) ∧ w ∈ e := by
    intro c hc
    have h' := (hTB c hc).2
    rw [← famVert_famOf (colourFam φ c), mem_famVert] at h'
    exact h'
  -- ## `|S| ≤ |T|`
  let f1 : Set (Fin n) → Fin n := fun e =>
    if h : e ∈ famUnionFinset (fun c => colourFam φ c) C ∧ w ∈ e
      then (existsUnique_colour_of_mem_union h.1).choose else w
  have hf1 : ∀ e ∈ S, f1 e ∈ T := by
    intro e he
    obtain ⟨he1, he2⟩ := hexA e he
    have hfe : f1 e = (existsUnique_colour_of_mem_union he1).choose := by
      simp only [f1]; rw [dif_pos ⟨he1, he2⟩]
    rw [hfe, hT, finalColoursAt, Finset.mem_coe, Finset.mem_filter]
    exact ⟨(existsUnique_colour_of_mem_union he1).choose_spec.1.1, by
      rw [← famVert_famOf (colourFam φ _), mem_famVert]
      exact ⟨e, (existsUnique_colour_of_mem_union he1).choose_spec.1.2, he2⟩⟩
  have hf1inj : Set.InjOn f1 S := by
    intro e he e' he' heq
    obtain ⟨he1, he2⟩ := hexA e he
    obtain ⟨he'1, he'2⟩ := hexA e' he'
    have h1 : f1 e = (existsUnique_colour_of_mem_union he1).choose := by
      simp only [f1]; rw [dif_pos ⟨he1, he2⟩]
    have h2 : f1 e' = (existsUnique_colour_of_mem_union he'1).choose := by
      simp only [f1]; rw [dif_pos ⟨he'1, he'2⟩]
    have hc : (existsUnique_colour_of_mem_union he1).choose =
        (existsUnique_colour_of_mem_union he'1).choose := h1.symm.trans (heq.trans h2)
    have hmem' : e ∈ famOf (colourFam φ (existsUnique_colour_of_mem_union he'1).choose) := by
      rw [← hc]
      exact (existsUnique_colour_of_mem_union he1).choose_spec.1.2
    exact eq_of_mem_famOf_colourFam_of_mem hmem'
      (existsUnique_colour_of_mem_union he'1).choose_spec.1.2 he2 he'2
  have hle1 : S.ncard ≤ T.ncard :=
    Set.ncard_le_ncard_of_injOn f1 hf1 hf1inj
  -- ## `|T| ≤ |S|`
  let f2 : Fin n → Set (Fin n) := fun c =>
    if h : c ∈ T then (hexB2 c h).choose else ∅
  have hf2 : ∀ c ∈ T, f2 c ∈ S := by
    intro c hc
    have hfc : f2 c = (hexB2 c hc).choose := by simp only [f2]; rw [dif_pos hc]
    rw [hfc, hS]
    exact ⟨mem_famUnionFinset.mpr ⟨c, (hTB c hc).1, (hexB2 c hc).choose_spec.1⟩,
      (hexB2 c hc).choose_spec.2⟩
  have hf2inj : Set.InjOn f2 T := by
    intro c hc c' hc' heq
    have h2 : f2 c = (hexB2 c hc).choose := by simp only [f2]; rw [dif_pos hc]
    have h2' : f2 c' = (hexB2 c' hc').choose := by simp only [f2]; rw [dif_pos hc']
    have hee : (hexB2 c hc).choose = (hexB2 c' hc').choose := h2.symm.trans (heq.trans h2')
    obtain ⟨e₁, he₁, heq₁⟩ := mem_famOf.mp (hexB2 c hc).choose_spec.1
    obtain ⟨e₂, he₂, heq₂⟩ := mem_famOf.mp (hexB2 c' hc').choose_spec.1
    have heq12 : e₁ = e₂ := Subtype.ext (heq₁.trans (hee.trans heq₂.symm))
    exact colourFam_eq_of_mem he₁ (heq12 ▸ he₂)
  have hle2 : T.ncard ≤ S.ncard := Set.ncard_le_ncard_of_injOn f2 hf2 hf2inj
  have hcard : S.ncard = T.ncard := le_antisymm hle1 hle2
  rw [hS] at hcard
  rw [hT] at hcard
  rw [← Set.ncard_coe_finset]
  exact hcard

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Pairwise edge-disjointness of the four families of `𝓜_prev` -/

/-- **The four families of `𝓜_prev` are pairwise edge-disjoint.**  This is the
disjointness used in the degree estimate `s12_deg_h_final`; it follows from the
inclusions `R₁ ∩ ⋃𝓜_diff = ∅`, `R₂ ⊆ R₁ ∖ ⋃𝓜_hm`, `R₃ ⊆ R₂ ∖ ⋃N` and
`𝓗_rem ⊆ 𝓗_small ∖ (R_res ∪ ⋃𝓜_diff ∪ ⋃N)` together with the pairwise
disjointness of the matchings within each step and the fact that the *added*
edges of every step have size at most `r₁` while the colour classes have size
more than `r₁`. -/
theorem prevFam_pairwise_disjoint {𝓗 : Hypergraph (Fin n)} {r₁ : ℕ}
    {φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n)}
    {MD HM MM MB : Fin n → Set 𝓗} {Cmed Cdiff Chuge Cmain Cbuff Cprev : Finset (Fin n)}
    {R_res R₁ R₂ R₃ 𝓗rem : Hypergraph (Fin n)} {ι : Type*} [Fintype ι]
    {N : ι → Set (Set (Fin n))}
    (hCprev : Cprev = Cmed ∪ Cdiff ∪ Chuge ∪ Cmain ∪ Cbuff)
    (hCmedD : Disjoint Cmed Cdiff)
    (hChuge_nd : ∀ c ∈ Chuge, c ∉ Cmed ∪ Cdiff)
    (hCmain_nd : ∀ c ∈ Cmain, c ∉ Cmed ∪ Cdiff ∪ Chuge)
    (hCbuff_nd : ∀ c ∈ Cbuff, c ∉ Cmed ∪ Cdiff ∪ Chuge ∪ Cmain)
    (hDcard : Cdiff.card ≤ 1)
    -- colour classes and added edges
    (hcolBig : ∀ c ∈ Cprev, ∀ e ∈ famOf (colourFam φ c), (r₁ : ℝ) < (edgeSize e : ℝ))
    (haddBig : ∀ x ∈ Cprev, ∀ f ∈ prevFam MD HM MM MB Cdiff Cmain Cbuff x,
      f ∉ famOf (colourFam φ x) → (edgeSize f : ℝ) ≤ (r₁ : ℝ))
    (hDadd : ∀ c ∈ Cdiff, famOf (MD c) ⊆ famOf (colourFam φ c) ∪ 𝓗.pow2)
    (hHadd : ∀ c ∈ Cmed ∪ Chuge, famOf (HM c) ⊆ famOf (colourFam φ c) ∪ R₁)
    (hMadd : ∀ c ∈ Cmain, famOf (MM c) ⊆ famOf (colourFam φ c) ∪
      ((𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset MD Cdiff)) ∪ R₂))
    (hBadd : ∀ c ∈ Cbuff, famOf (MB c) ⊆ famOf (colourFam φ c) ∪ (𝓗rem ∪ R₃))
    (hMN : ∀ c ∈ Cmain, famOf (MM c) ⊆ famOf (colourFam φ c) ∪ (⋃ i, N i))
    -- the bookkeeping facts
    (hMD_R₁ : Disjoint (famUnionFinset MD Cdiff) R₁)
    (hHM_R₂ : Disjoint (famUnionFinset HM (Cmed ∪ Chuge)) R₂)
    (hR₂R₁ : R₂ ⊆ R₁) (hR₃R₂ : R₃ ⊆ R₂) (hR₁res : R₁ ⊆ R_res)
    (hR₃N : R₃ ⊆ R₂ \ (⋃ i, N i))
    (hrem : 𝓗rem ⊆ 𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset MD Cdiff ∪ (⋃ i, N i)))
    (hHdisj : ∀ c ∈ Cmed ∪ Chuge, ∀ c' ∈ Cmed ∪ Chuge, c ≠ c' →
      Disjoint (famOf (HM c)) (famOf (HM c')))
    (hMdisj : ∀ c ∈ Cmain, ∀ c' ∈ Cmain, c ≠ c' →
      Disjoint (famOf (MM c)) (famOf (MM c')))
    (hBdisj : ∀ c ∈ Cbuff, ∀ c' ∈ Cbuff, c ≠ c' →
      Disjoint (famOf (MB c)) (famOf (MB c')))
    (hcoldisj : ∀ c c' : Fin n, c ≠ c' →
      Disjoint (famOf (colourFam φ c)) (famOf (colourFam φ c'))) :
    ∀ c ∈ Cprev, ∀ c' ∈ Cprev, c ≠ c' →
      Disjoint (prevFam MD HM MM MB Cdiff Cmain Cbuff c)
        (prevFam MD HM MM MB Cdiff Cmain Cbuff c') := by
  classical
  have htag : ∀ x ∈ Cprev, x ∈ Cdiff ∨ x ∈ Cmain ∨ x ∈ Cbuff ∨ x ∈ Cmed ∪ Chuge := by
    intro x hx
    rw [hCprev] at hx
    simp only [Finset.mem_union] at hx ⊢
    tauto
  -- membership of `c ∈ Cdiff` etc. from the tag hypotheses
  have hCdiff_of_main : ∀ x ∈ Cmain, x ∉ Cdiff := fun x hx hh =>
    (hCmain_nd x hx) (Finset.mem_union_left Chuge (Finset.mem_union_right Cmed hh))
  have hCdiff_of_buff : ∀ x ∈ Cbuff, x ∉ Cdiff := fun x hx hh =>
    (hCbuff_nd x hx) (Finset.mem_union_left Cmain (Finset.mem_union_left Chuge
      (Finset.mem_union_right Cmed hh)))
  have hCmain_of_buff : ∀ x ∈ Cbuff, x ∉ Cmain := fun x hx hh =>
    (hCbuff_nd x hx) (Finset.mem_union_right (Cmed ∪ Cdiff ∪ Chuge) hh)
  have hCdiff_of_H : ∀ x ∈ Cmed ∪ Chuge, x ∉ Cdiff := by
    intro x hx hh
    rcases Finset.mem_union.mp hx with h5 | h5
    · exact Finset.disjoint_left.mp hCmedD h5 hh
    · exact hChuge_nd x h5 (Finset.mem_union_right Cmed hh)
  have hCmedChuge : ∀ x ∈ Cmed ∪ Chuge, x ∈ Cmed ∪ Cdiff ∪ Chuge := by
    intro x hx
    rcases Finset.mem_union.mp hx with h1 | h1
    · exact Finset.mem_union_left Chuge (Finset.mem_union_left Cdiff h1)
    · exact Finset.mem_union_right (Cmed ∪ Cdiff) h1
  have hCmain_of_H : ∀ x ∈ Cmed ∪ Chuge, x ∉ Cmain := fun x hx hh =>
    (hCmain_nd x hh) (hCmedChuge x hx)
  have hCbuff_of_H : ∀ x ∈ Cmed ∪ Chuge, x ∉ Cbuff := fun x hx hh =>
    (hCbuff_nd x hh) (Finset.mem_union_left Cmain (hCmedChuge x hx))
  intro c hc c' hc' hne
  rw [Set.disjoint_left]
  intro e he he'
  -- the decomposition of `e ∈ 𝓜_prev(x)`
  have hfam : ∀ x ∈ Cprev, e ∈ prevFam MD HM MM MB Cdiff Cmain Cbuff x →
      e ∈ famOf (colourFam φ x) ∨
      (e ∉ famOf (colourFam φ x) ∧
        ((x ∈ Cdiff ∧ e ∈ famOf (MD x)) ∨ (x ∈ Cmed ∪ Chuge ∧ e ∈ famOf (HM x)) ∨
         (x ∈ Cmain ∧ e ∈ famOf (MM x)) ∨ (x ∈ Cbuff ∧ e ∈ famOf (MB x)))) := by
    intro x hx hxe
    rcases htag x hx with h | h | h | h
    · rw [prevFam_of_mem_Cdiff h] at hxe
      by_cases hc : e ∈ famOf (colourFam φ x)
      · exact Or.inl hc
      · exact Or.inr ⟨hc, Or.inl ⟨h, hxe⟩⟩
    · rw [prevFam_of_mem_Cmain (hCdiff_of_main x h) h] at hxe
      by_cases hc : e ∈ famOf (colourFam φ x)
      · exact Or.inl hc
      · exact Or.inr ⟨hc, Or.inr (Or.inr (Or.inl ⟨h, hxe⟩))⟩
    · rw [prevFam_of_mem_Cbuff (hCdiff_of_buff x h) (hCmain_of_buff x h) h] at hxe
      by_cases hc : e ∈ famOf (colourFam φ x)
      · exact Or.inl hc
      · exact Or.inr ⟨hc, Or.inr (Or.inr (Or.inr ⟨h, hxe⟩))⟩
    · rw [prevFam_of_notMem (hCdiff_of_H x h) (hCmain_of_H x h) (hCbuff_of_H x h)] at hxe
      by_cases hc : e ∈ famOf (colourFam φ x)
      · exact Or.inl hc
      · exact Or.inr ⟨hc, Or.inr (Or.inl ⟨h, hxe⟩)⟩
  -- the location lemmas
  have locH : ∀ x ∈ Cmed ∪ Chuge, e ∈ famOf (HM x) →
      e ∉ famOf (colourFam φ x) → e ∈ R₁ := fun x hx hf hn => by
    rcases hHadd x hx hf with h | h
    · exact absurd h hn
    · exact h
  have locM : ∀ x ∈ Cmain, e ∈ famOf (MM x) → e ∉ famOf (colourFam φ x) →
      e ∈ (𝓗.smallEdges r₁ \ (R_res ∪ famUnionFinset MD Cdiff)) ∪ R₂ := fun x hx hf hn => by
    rcases hMadd x hx hf with h | h
    · exact absurd h hn
    · exact h
  have locB : ∀ x ∈ Cbuff, e ∈ famOf (MB x) → e ∉ famOf (colourFam φ x) →
      e ∈ 𝓗rem ∪ R₃ := fun x hx hf hn => by
    rcases hBadd x hx hf with h | h
    · exact absurd h hn
    · exact h
  have locN : ∀ x ∈ Cmain, e ∈ famOf (MM x) → e ∉ famOf (colourFam φ x) →
      e ∈ (⋃ i, N i) := fun x hx hf hn => by
    rcases hMN x hx hf with h | h
    · exact absurd h hn
    · exact h
  have memMD : ∀ x ∈ Cdiff, e ∈ famOf (MD x) → e ∈ famUnionFinset MD Cdiff :=
    fun x hx hf => mem_famUnionFinset.mpr ⟨x, hx, hf⟩
  have memHM : ∀ x ∈ Cmed ∪ Chuge, e ∈ famOf (HM x) →
      e ∈ famUnionFinset HM (Cmed ∪ Chuge) := fun x hx hf =>
    mem_famUnionFinset.mpr ⟨x, hx, hf⟩
  rcases hfam c hc he with hcol | ⟨hcol, hcase⟩
  · rcases hfam c' hc' he' with hcol' | ⟨hcol', hcase'⟩
    · exact Set.disjoint_left.mp (hcoldisj c c' hne) hcol hcol'
    · have h1 := hcolBig c hc e hcol
      have h2 := haddBig c' hc' e he' hcol'
      linarith
  · rcases hfam c' hc' he' with hcol' | ⟨hcol', hcase'⟩
    · have h1 := hcolBig c' hc' e hcol'
      have h2 := haddBig c hc e he hcol
      linarith
    · rcases hcase with ⟨hDc, heMD⟩ | ⟨hHc, heHM⟩ | ⟨hMc, heMM⟩ | ⟨hBc, heMB⟩ <;>
      rcases hcase' with ⟨hDc', heMD'⟩ | ⟨hHc', heHM'⟩ | ⟨hMc', heMM'⟩ | ⟨hBc', heMB'⟩
      · exact absurd (Finset.card_le_one.mp hDcard c hDc c' hDc') hne
      · exact Set.disjoint_left.mp hMD_R₁ (memMD c hDc heMD) (locH c' hHc' heHM' hcol')
      · rcases locM c' hMc' heMM' hcol' with hin | hin
        · exact hin.2 (Or.inr (memMD c hDc heMD))
        · exact Set.disjoint_left.mp hMD_R₁ (memMD c hDc heMD) (hR₂R₁ hin)
      · rcases locB c' hBc' heMB' hcol' with hin | hin
        · exact (hrem hin).2 (Or.inl (Or.inr (memMD c hDc heMD)))
        · exact Set.disjoint_left.mp hMD_R₁ (memMD c hDc heMD) (hR₂R₁ (hR₃R₂ hin))
      · exact Set.disjoint_left.mp hMD_R₁ (memMD c' hDc' heMD') (locH c hHc heHM hcol)
      · exact Set.disjoint_left.mp (hHdisj c hHc c' hHc' hne) heHM heHM'
      · rcases locM c' hMc' heMM' hcol' with hin | hin
        · exact hin.2 (Or.inl (hR₁res (locH c hHc heHM hcol)))
        · exact Set.disjoint_left.mp hHM_R₂ (memHM c hHc heHM) hin
      · rcases locB c' hBc' heMB' hcol' with hin | hin
        · exact (hrem hin).2 (Or.inl (Or.inl (hR₁res (locH c hHc heHM hcol))))
        · exact Set.disjoint_left.mp hHM_R₂ (memHM c hHc heHM) (hR₃R₂ hin)
      · rcases locM c hMc heMM hcol with hin | hin
        · exact hin.2 (Or.inr (memMD c' hDc' heMD'))
        · exact Set.disjoint_left.mp hMD_R₁ (memMD c' hDc' heMD') (hR₂R₁ hin)
      · rcases locM c hMc heMM hcol with hin | hin
        · exact hin.2 (Or.inl (hR₁res (locH c' hHc' heHM' hcol')))
        · exact Set.disjoint_left.mp hHM_R₂ (memHM c' hHc' heHM') hin
      · exact Set.disjoint_left.mp (hMdisj c hMc c' hMc' hne) heMM heMM'
      · rcases locB c' hBc' heMB' hcol' with hin | hin
        · exact (hrem hin).2 (Or.inr (locN c hMc heMM hcol))
        · exact (hR₃N hin).2 (locN c hMc heMM hcol)
      · rcases locB c hBc heMB hcol with hin | hin
        · exact (hrem hin).2 (Or.inl (Or.inr (memMD c' hDc' heMD')))
        · exact Set.disjoint_left.mp hMD_R₁ (memMD c' hDc' heMD') (hR₂R₁ (hR₃R₂ hin))
      · rcases locB c hBc heMB hcol with hin | hin
        · exact (hrem hin).2 (Or.inl (Or.inl (hR₁res (locH c' hHc' heHM' hcol'))))
        · exact Set.disjoint_left.mp hHM_R₂ (memHM c' hHc' heHM') (hR₃R₂ hin)
      · rcases locB c hBc heMB hcol with hin | hin
        · exact (hrem hin).2 (Or.inr (locN c' hMc' heMM' hcol'))
        · exact (hR₃N hin).2 (locN c' hMc' heMM' hcol')
      · exact Set.disjoint_left.mp (hBdisj c hBc c' hBc' hne) heMB heMB'

end

end ErdosFaberLovaszConjecture
