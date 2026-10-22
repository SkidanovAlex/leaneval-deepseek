import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ANALYTIC.EA_shift
import Submission.Work.ANALYTIC.EA_natural
import Submission.Work.ATOM.ZS.HFour.Defs
import Submission.Work.ATOM.ZS.hFour_RED_R
import Submission.Work.ATOM.ZS.hFour_cover

namespace Work.ATOM.ZS

set_option linter.style.haveILetI false

open CategoryTheory Limits LightProfinite MonoidalCategory LightCondensed MonoidalClosed
open OnePoint

noncomputable section

variable (S : LightProfinite.{0}) [Infinite S]

/-- Functoriality of `zmap = ℤ[-]`. -/
lemma hFour_zmap_comp {X Y Z : LightProfinite.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Work.ATOM.zmap (f ≫ g) = Work.ATOM.zmap f ≫ Work.ATOM.zmap g :=
  Functor.map_comp _ _ _

/-- `EApp = EA (ℕ∪∞) ≫ (P ◁ P_proj)`: unfolding both definitions and reassociating. -/
lemma hFour_EApp_eq :
    Work.ATOM.EApp =
      Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ LightCondensed.P_proj) := by
  simp only [Work.ATOM.EApp, Work.ATOM.EA, Category.assoc]

/-- **The left hand side of `h₄` on the cover `(ℕ∪∞) × T'`.**  Pulling `EApp ≫ m ≫ G` back along
`hFourPull = id × tProj : (ℕ∪∞) × T' ⟶ (ℕ∪∞) × (ℕ∪∞)` and using the descent property
`Work.ATOM.gBig_spec` of `g` over `T'` turns it into the `zmap`-combination
`(zmap ψ₁ - zmap ψ₂) ≫ P_proj`, where `ψ₁(k,t) = ψ(k, pr₂ t)` and `ψ₂(k,t) = ψ(k, β t)`. -/
theorem hFour_RED_L :
    Work.ATOM.zmap (hFourPull S) ≫ Work.ATOM.EApp ≫ Work.ATOM.m S ≫ Work.ATOM.G S =
      (Work.ATOM.zmap (hFourPsi1 S) - Work.ATOM.zmap (hFourPsi2 S)) ≫ LightCondensed.P_proj := by
  -- the block `P ◁ P_proj ≫ P ◁ g` is `P ◁ gBig` (`Work.ATOM.g_spec`)
  have hwh : (LightCondensed.P ◁ LightCondensed.P_proj) ≫ (LightCondensed.P ◁ Work.ATOM.g S) ≫
      Work.ATOM.G S =
      (LightCondensed.P ◁ Work.ATOM.gBig S) ≫ Work.ATOM.G S := by
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, Work.ATOM.g_spec]
  -- step 1: `EApp ≫ m ≫ G = EA (ℕ∪∞) ≫ (P ◁ gBig) ≫ G`
  have hA : Work.ATOM.EApp ≫ Work.ATOM.m S ≫ Work.ATOM.G S =
      Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ Work.ATOM.gBig S) ≫ Work.ATOM.G S := by
    simp only [hFour_EApp_eq, Work.ATOM.m, Category.assoc]
    rw [hwh]
  -- step 2: naturality of `EA` along `tProj : T' ⟶ ℕ∪∞`
  have hnat : Work.ATOM.zmap (hFourPull S) ≫ Work.ATOM.EA (ℕ∪{∞}) =
      Work.ATOM.EA (Work.ATOM.T' S) ≫
        (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.tProj S)) :=
    (Work.ANALYTIC.EA_natural (T := Work.ATOM.T' S) (S := ℕ∪{∞}) (Work.ATOM.tProj S)).symm
  -- step 3: the block `P ◁ zmap tProj ≫ P ◁ gBig` is `P ◁ gHat`
  have hwh2 : (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.tProj S)) ≫
      (LightCondensed.P ◁ Work.ATOM.gBig S) ≫ Work.ATOM.G S =
      (LightCondensed.P ◁ Work.ATOM.gHat S) ≫ Work.ATOM.G S := by
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, Work.ATOM.gBig_spec]
  -- step 4: naturality of `EA` along `pr₂T : T' ⟶ S`, and `EA S ≫ G = zmap ψ ≫ P_proj`
  have hnatR : Work.ATOM.EA (Work.ATOM.T' S) ≫
        (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.pr₂T S)) ≫ Work.ATOM.G S =
      Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) (Work.ATOM.pr₂T S)) ≫
        Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj := by
    rw [← Category.assoc, Work.ANALYTIC.EA_natural (T := Work.ATOM.T' S) (S := S)
      (Work.ATOM.pr₂T S)]
    simp only [Category.assoc, Work.ATOM.G_spec, Work.ATOM.Gsection]
  have hnatB : Work.ATOM.EA (Work.ATOM.T' S) ≫
        (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.betaT S)) ≫ Work.ATOM.G S =
      Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) (Work.ATOM.betaT S)) ≫
        Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj := by
    rw [← Category.assoc, Work.ANALYTIC.EA_natural (T := Work.ATOM.T' S) (S := S)
      (Work.ATOM.betaT S)]
    simp only [Category.assoc, Work.ATOM.G_spec, Work.ATOM.Gsection]
  -- step 5: the two `zmap`s combine
  have hcomb1 : Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) (Work.ATOM.pr₂T S)) ≫
      Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj =
      Work.ATOM.zmap (hFourPsi1 S) ≫ LightCondensed.P_proj := by
    rw [← Category.assoc, ← hFour_zmap_comp]; rfl
  have hcomb2 : Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) (Work.ATOM.betaT S)) ≫
      Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj =
      Work.ATOM.zmap (hFourPsi2 S) ≫ LightCondensed.P_proj := by
    rw [← Category.assoc, ← hFour_zmap_comp]; rfl
  calc Work.ATOM.zmap (hFourPull S) ≫ Work.ATOM.EApp ≫ Work.ATOM.m S ≫ Work.ATOM.G S
      = Work.ATOM.zmap (hFourPull S) ≫
          (Work.ATOM.EApp ≫ Work.ATOM.m S ≫ Work.ATOM.G S) := by
          simp only [Category.assoc]
    _ = Work.ATOM.zmap (hFourPull S) ≫
          (Work.ATOM.EA (ℕ∪{∞}) ≫ (LightCondensed.P ◁ Work.ATOM.gBig S) ≫
            Work.ATOM.G S) := by rw [hA]
    _ = (Work.ATOM.zmap (hFourPull S) ≫ Work.ATOM.EA (ℕ∪{∞})) ≫
          (LightCondensed.P ◁ Work.ATOM.gBig S) ≫ Work.ATOM.G S := by
          simp only [Category.assoc]
    _ = (Work.ATOM.EA (Work.ATOM.T' S) ≫
            (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.tProj S))) ≫
          (LightCondensed.P ◁ Work.ATOM.gBig S) ≫ Work.ATOM.G S := by rw [hnat]
    _ = Work.ATOM.EA (Work.ATOM.T' S) ≫
          (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.tProj S)) ≫
            (LightCondensed.P ◁ Work.ATOM.gBig S) ≫ Work.ATOM.G S := by
          simp only [Category.assoc]
    _ = Work.ATOM.EA (Work.ATOM.T' S) ≫ (LightCondensed.P ◁ Work.ATOM.gHat S) ≫
          Work.ATOM.G S := by rw [hwh2]
    _ = Work.ATOM.EA (Work.ATOM.T' S) ≫
          (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.pr₂T S) -
            LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.betaT S)) ≫ Work.ATOM.G S := by
          rw [Work.ATOM.gHat, hFour_whiskerLeft_sub]
    _ = Work.ATOM.EA (Work.ATOM.T' S) ≫
          ((LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.pr₂T S)) ≫ Work.ATOM.G S -
            (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.betaT S)) ≫ Work.ATOM.G S) := by
          rw [Preadditive.sub_comp]
    _ = (Work.ATOM.EA (Work.ATOM.T' S) ≫
            (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.pr₂T S)) ≫ Work.ATOM.G S) -
          (Work.ATOM.EA (Work.ATOM.T' S) ≫
            (LightCondensed.P ◁ Work.ATOM.zmap (Work.ATOM.betaT S)) ≫ Work.ATOM.G S) := by
          rw [Preadditive.comp_sub]
    _ = (Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) (Work.ATOM.pr₂T S)) ≫
            Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj) -
          (Work.ATOM.zmap (MonoidalCategory.whiskerLeft (ℕ∪{∞}) (Work.ATOM.betaT S)) ≫
            Work.ATOM.zmap (Work.ATOM.psiN S) ≫ LightCondensed.P_proj) := by
          rw [hnatR, hnatB]
    _ = (Work.ATOM.zmap (hFourPsi1 S) - Work.ATOM.zmap (hFourPsi2 S)) ≫
          LightCondensed.P_proj := by
          rw [hcomb1, hcomb2, ← Preadditive.sub_comp]

lemma hFour_ICA_zmap_psi : Work.ATOM.zmap (hFourICA S) ≫ Work.ATOM.zmap (hFourPsi1 S) =
    Work.ATOM.zmap (hFourICA S) ≫ Work.ATOM.zmap (hFourPsi2 S) := by
  rw [← Functor.map_comp, ← Functor.map_comp, hFourICA_psi]

lemma hFour_ICA_zmap_q : Work.ATOM.zmap (hFourICA S) ≫ Work.ATOM.zmap (hFourQ1 S) =
    Work.ATOM.zmap (hFourICA S) ≫ Work.ATOM.zmap (hFourQ2 S) := by
  rw [← Functor.map_comp, ← Functor.map_comp, hFourICA_q]

lemma hFour_ICB_zmap : Work.ATOM.zmap (hFourICB S) ≫
      (Work.ATOM.zmap (hFourPsi1 S) - Work.ATOM.zmap (hFourPsi2 S)) =
    Work.ATOM.zmap (hFourICB S) ≫
      (Work.ATOM.zmap (hFourQ1 S) - Work.ATOM.zmap (hFourQ2 S)) := by
  rw [Preadditive.comp_sub, Preadditive.comp_sub, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, hFourICB_psi1, hFourICB_psi2]

/-- **Identity `h₄` of REFS/03 §1**: `(id_P ⊗ g) ≫ G = ((1-S) ⊗ id_P) ≫ F_P` (this is the
*definition* of `G_P` in the source).  On generators `(k,j)`: the left side is
`e_{ψ(k,a_j)} - e_{ψ(k,e_{n(j)-1}a_j)}` and the right side is `F_P(k,j) - F_P(k+1,j)`, which is
`e_j` when `k = n(j)` and `0` otherwise (`Work.ATOM.phiP_some_some_of_le`,
`Work.ATOM.phiP_some_some_of_lt`).  For `k < n(j)` the two `ψ`-values agree because
`e_k e_{n(j)-1} = e_k`; for `k > n(j)` both terms vanish because `e_k a_j = a_j` has level
`n(j) < k`. -/
theorem h_four (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.m S ≫ Work.ATOM.G S = Work.ATOM.preShiftP ≫ Work.ATOM.FP S := by
  -- the two sides become `zmap`-combinations on the closed cover `(ℕ∪∞) × T'`
  have hco : ∀ w : ↥(hFourW S), w ∈ hFourCA S ∨ w ∈ hFourCB S := hFour_cover S
  haveI : Epi Work.ATOM.EApp := hFour_epi_EApp
  refine (cancel_epi (Work.ATOM.EApp)).mp ?_
  refine Work.ATOM.zmap_ext_of_closed_cover _ _ 1 (fun _ => hFourW S)
    (fun _ => hFourPull S) ?_ ?_
  · intro t
    exact ⟨0, hFourPull_surjective S t⟩
  · intro i
    rw [hFour_RED_L S, hFour_RED_R S]
    refine Work.ATOM.zmap_ext_of_closed_cover _ _ 2 (hFourCover S) (hFourCoverι S) ?_ ?_
    · intro t
      rcases hco t with h | h
      · exact ⟨0, mem_range_hFourICA S h⟩
      · exact ⟨1, mem_range_hFourICB S h⟩
    · intro i
      fin_cases i
      · have h1 : Work.ATOM.zmap (hFourICA S) ≫
            (Work.ATOM.zmap (hFourPsi1 S) - Work.ATOM.zmap (hFourPsi2 S)) = 0 := by
          rw [Preadditive.comp_sub, hFour_ICA_zmap_psi, sub_self]
        have h2 : Work.ATOM.zmap (hFourICA S) ≫
            (Work.ATOM.zmap (hFourQ1 S) - Work.ATOM.zmap (hFourQ2 S)) = 0 := by
          rw [Preadditive.comp_sub, hFour_ICA_zmap_q, sub_self]
        show Work.ATOM.zmap (hFourICA S) ≫
              (Work.ATOM.zmap (hFourPsi1 S) - Work.ATOM.zmap (hFourPsi2 S)) ≫
                LightCondensed.P_proj =
            Work.ATOM.zmap (hFourICA S) ≫
              (Work.ATOM.zmap (hFourQ1 S) - Work.ATOM.zmap (hFourQ2 S)) ≫
                LightCondensed.P_proj
        simp only [← Category.assoc, h1, h2, zero_comp]
      · show Work.ATOM.zmap (hFourICB S) ≫
              (Work.ATOM.zmap (hFourPsi1 S) - Work.ATOM.zmap (hFourPsi2 S)) ≫
                LightCondensed.P_proj =
            Work.ATOM.zmap (hFourICB S) ≫
              (Work.ATOM.zmap (hFourQ1 S) - Work.ATOM.zmap (hFourQ2 S)) ≫
                LightCondensed.P_proj
        simp only [← Category.assoc, hFour_ICB_zmap]

end

end Work.ATOM.ZS
