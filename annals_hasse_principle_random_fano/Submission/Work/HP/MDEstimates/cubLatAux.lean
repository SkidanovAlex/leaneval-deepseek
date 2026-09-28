import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.ballCount_le_pow_rk
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.Sig2.Tset_finite
import Submission.Work.Q44Geom.Setup
import Submission.Work.Q44Geom.BadDefs
import Submission.Work.Q44Geom.zero_count
import Submission.Work.Q44Geom.ncard_le_planeSet_ncard
import Submission.Work.HP.MDEstimates.vanishRatSpanCub

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

open MvPolynomial

namespace Work.HP.MDEstimates

/-! ## Elementary helpers -/

/-- `LinearIndependent` for a `Fin 2`-indexed family transfers to the pair notation. -/
lemma linIndep_fin2_to_pair {f : Fin 2 → (Fin 5 → ℤ)} (h : LinearIndependent ℤ f) :
    LinearIndependent ℤ ![f 0, f 1] := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have hsum : (∑ j : Fin 2, g j • f j) = 0 := by
    have h1 : (∑ j : Fin 2, g j • (![f 0, f 1] j)) = ∑ j : Fin 2, g j • f j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      fin_cases j <;> simp
    rw [← h1]; exact hg
  exact h g hsum i

lemma pair_fst_ne_zero {x y : Fin 5 → ℤ} (h : LinearIndependent ℤ ![x, y]) : x ≠ 0 := by
  intro h0
  have h1 : (1 : ℤ) = 0 := by
    have hsum : (∑ j : Fin 2, (![1, 0] : Fin 2 → ℤ) j • ![x, y] j) = 0 := by
      rw [Fin.sum_univ_two]; simp [h0]
    simpa using (Fintype.linearIndependent_iff.mp h ![1, 0] hsum 0)
  exact absurd h1 (by norm_num)

lemma pair_snd_ne_zero {x y : Fin 5 → ℤ} (h : LinearIndependent ℤ ![x, y]) : y ≠ 0 := by
  intro h0
  have h1 : (1 : ℤ) = 0 := by
    have hsum : (∑ j : Fin 2, (![0, 1] : Fin 2 → ℤ) j • ![x, y] j) = 0 := by
      rw [Fin.sum_univ_two]; simp [h0]
    simpa using (Fintype.linearIndependent_iff.mp h ![0, 1] hsum 1)
  exact absurd h1 (by norm_num)

lemma toRatLM_ne_zero {v : Fin 5 → ℤ} (h : v ≠ 0) : Work.Q44Geom.toRatLM v ≠ 0 := by
  intro h0
  refine h (funext fun i => ?_)
  have hi : ((v i : ℤ) : ℚ) = 0 := by
    have := congrFun h0 i
    simpa [Work.Q44Geom.toRatLM] using this
  exact_mod_cast hi

/-- Independence over `ℤ` of an integral pair gives independence over `ℚ` of its coercion. -/
lemma linIndep_rat_pair {x y : Fin 5 → ℤ} (h : LinearIndependent ℤ ![x, y]) :
    LinearIndependent ℚ ![Work.Q44Geom.toRatLM x, Work.Q44Geom.toRatLM y] := by
  have h' := (Work.HP.Q44Child.lamAttained_linIndep_iff ![x, y]).mp h
  rw [show (fun j : Fin 2 => fun i => (![x, y] j i : ℚ))
      = ![Work.Q44Geom.toRatLM x, Work.Q44Geom.toRatLM y] from by
    funext j i
    fin_cases j <;> rfl] at h'
  exact h'

/-- The first two successive-minimum vectors of a rank-3 lattice. -/
lemma exists_short_pair (L : Submodule ℤ (Fin 5 → ℤ)) (hLrk : Work.HP.rk L = 3) :
    ∃ f : Fin 2 → (Fin 5 → ℤ), (∀ i, f i ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ i, Work.HP.eNorm (f i) ≤ Work.HP.lam L (i.val + 1) :=
  Work.HP.Q44Child.lam_attained L 2 (by norm_num) (by omega)

/-! ## The counting sets -/

/-- The set counted by `cubLatCount`. -/
def CubLatSet (B : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
    (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
    (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => (x i : ℚ)) B = 0)}

/-- A canonical pair of short vectors of a member of `CubLatSet B s`. -/
noncomputable def cubPair (B : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ)
    (L : Submodule ℤ (Fin 5 → ℤ)) : (Fin 5 → ℤ) × (Fin 5 → ℤ) := by
  classical
  exact if h : L ∈ CubLatSet B s then
    ((Classical.choose (exists_short_pair L h.2.1)) 0,
     (Classical.choose (exists_short_pair L h.2.1)) 1)
  else (0, 0)

lemma cubPair_spec {B : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ∈ CubLatSet B s) :
    (cubPair B s L).1 ∈ L ∧ (cubPair B s L).2 ∈ L ∧
    LinearIndependent ℤ ![(cubPair B s L).1, (cubPair B s L).2] ∧
    Work.HP.eNorm (cubPair B s L).1 ≤ s 0 ∧ Work.HP.eNorm (cubPair B s L).2 ≤ s 1 := by
  classical
  have h := Classical.choose_spec (exists_short_pair L hL.2.1)
  have hdef : cubPair B s L = ((Classical.choose (exists_short_pair L hL.2.1)) 0,
      (Classical.choose (exists_short_pair L hL.2.1)) 1) := by
    rw [cubPair]
    exact dif_pos hL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdef]; exact h.1 0
  · rw [hdef]; exact h.1 1
  · rw [hdef]; exact linIndep_fin2_to_pair h.2.1
  · rw [hdef]
    have h2 := h.2.2 0
    simp only [Fin.val_zero] at h2
    exact le_trans h2 (by simpa using hL.2.2.1 0)
  · rw [hdef]
    have h2 := h.2.2 1
    simp only [Fin.val_one] at h2
    exact le_trans h2 (by simpa using hL.2.2.1 1)

/-- The "good" members of the counting set: the canonical pair is not contained in the
invariance subspace. -/
def CubGood (B : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ)
    (L : Submodule ℤ (Fin 5 → ℤ)) : Prop :=
  L ∈ CubLatSet B s ∧
    (Work.Q44Geom.toRatLM (cubPair B s L).1 ∉ Work.Q44Geom.invSub B ∨
     Work.Q44Geom.toRatLM (cubPair B s L).2 ∉ Work.Q44Geom.invSub B)

/-- The "bad" members of the counting set: both canonical vectors lie in the invariance
subspace. -/
def CubBad (B : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ)
    (L : Submodule ℤ (Fin 5 → ℤ)) : Prop :=
  L ∈ CubLatSet B s ∧ ¬
    (Work.Q44Geom.toRatLM (cubPair B s L).1 ∉ Work.Q44Geom.invSub B ∨
     Work.Q44Geom.toRatLM (cubPair B s L).2 ∉ Work.Q44Geom.invSub B)

/-- The plane set attached to a pair of integral vectors. -/
def CubPlaneSet (B : MvPolynomial (Fin 5) ℚ) (x y : Fin 5 → ℤ) :
    Set (Submodule ℚ (Fin 5 → ℚ)) :=
  {P | Module.finrank ℚ P = 3 ∧ Work.Q44Geom.toRatLM x ∈ P ∧ Work.Q44Geom.toRatLM y ∈ P ∧
    ∀ z ∈ P, MvPolynomial.eval z B = 0}

/-- The possible canonical pairs of the good members. -/
def CubPairs (B : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ) :
    Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | Work.HP.eNorm p.1 ≤ s 0 ∧ Work.HP.eNorm p.2 ≤ s 1 ∧
    MvPolynomial.eval (Work.Q44Geom.toRatLM p.1) B = 0 ∧
    MvPolynomial.eval (Work.Q44Geom.toRatLM p.2) B = 0}

lemma CubLatSet_finite {B : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ} :
    (CubLatSet B s).Finite :=
  (Work.HP.Sig2.Tset_finite (ι := Fin 5) 3 s).subset fun L hL =>
    ⟨hL.1, hL.2.1, hL.2.2.1⟩

lemma CubGood_finite {B : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ} :
    {L : Submodule ℤ (Fin 5 → ℤ) | CubGood B s L}.Finite :=
  CubLatSet_finite.subset fun L hL => hL.1

lemma CubBad_finite {B : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ} :
    {L : Submodule ℤ (Fin 5 → ℤ) | CubBad B s L}.Finite :=
  CubLatSet_finite.subset fun L hL => hL.1

lemma cubPairs_finite {B : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ} :
    (CubPairs B s).Finite := by
  refine (Work.HP.MDBasic.finite_eNorm_le (s 0)).prod
    (Work.HP.MDBasic.finite_eNorm_le (s 1)) |>.subset ?_
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

/-- A member of the bad set has both canonical vectors in the invariance lattice, and
`L ⊓ latW B` has rank at least `2`. -/
lemma bad_pair_mem {B : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ}
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : CubBad B s L) :
    (cubPair B s L).1 ∈ Work.Q44Geom.latW B ∧ (cubPair B s L).2 ∈ Work.Q44Geom.latW B ∧
      2 ≤ Work.HP.rk (L ⊓ Work.Q44Geom.latW B) := by
  obtain ⟨hLset, hbad⟩ := hL
  push Not at hbad
  obtain ⟨h1, h2⟩ := hbad
  have hspec := cubPair_spec hLset
  refine ⟨Work.Q44Geom.mem_latW_iff.mpr h1, Work.Q44Geom.mem_latW_iff.mpr h2, ?_⟩
  exact Work.Q44Geom.two_le_rk_of_linIndep
    (Submodule.mem_inf.mpr ⟨hspec.1, Work.Q44Geom.mem_latW_iff.mpr h1⟩)
    (Submodule.mem_inf.mpr ⟨hspec.2.1, Work.Q44Geom.mem_latW_iff.mpr h2⟩)
    hspec.2.2.1

/-- In the rank-`2` case, a bad member of the counting set contains the whole invariance
lattice. -/
lemma bad_contains_latW {B : MvPolynomial (Fin 5) ℚ} {s : Fin 3 → ℝ}
    (hW2 : Work.HP.rk (Work.Q44Geom.latW B) = 2)
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : CubBad B s L) :
    Work.Q44Geom.latW B ≤ L := by
  obtain ⟨-, -, hrk⟩ := bad_pair_mem hL
  have hLE : Work.HP.rk (L ⊓ Work.Q44Geom.latW B) ≤ Work.HP.rk (Work.Q44Geom.latW B) :=
    Submodule.finrank_mono (inf_le_right : L ⊓ Work.Q44Geom.latW B ≤ Work.Q44Geom.latW B)
  rw [hW2] at hLE
  have hrk2 : Work.HP.rk (L ⊓ Work.Q44Geom.latW B) = 2 := le_antisymm hLE hrk
  have hprim : Work.HP.IsPrimLat (L ⊓ Work.Q44Geom.latW B) :=
    Work.Q44Geom.isPrimLat_inf hL.1.1 (Work.Q44Geom.isPrimLat_latW B)
  have hspan : Work.Q44Geom.ratSpan (L ⊓ Work.Q44Geom.latW B)
      = Work.Q44Geom.ratSpan (Work.Q44Geom.latW B) := by
    refine Submodule.eq_of_le_of_finrank_eq (Work.Q44Geom.ratSpan_mono inf_le_right) ?_
    rw [Work.Q44Geom.ratSpan_finrank_general, Work.Q44Geom.ratSpan_finrank_general, hrk2, hW2]
  have heq : L ⊓ Work.Q44Geom.latW B = Work.Q44Geom.latW B :=
    Work.Q44Geom.ratSpan_injective_of_isPrimLat hprim (Work.Q44Geom.isPrimLat_latW B) hspan
  rw [← heq]
  exact inf_le_left

/-- The map `L ↦ ratSpan L` injects any family of good members with a fixed canonical pair
into the corresponding plane set. -/
lemma ncard_le_cubPlaneSet {B : MvPolynomial (Fin 5) ℚ} (hB : B.IsHomogeneous 3)
    {s : Fin 3 → ℝ} {x y : Fin 5 → ℤ} (T : Set (Submodule ℤ (Fin 5 → ℤ)))
    (hT : ∀ L ∈ T, L ∈ CubLatSet B s ∧ (cubPair B s L).1 = x ∧ (cubPair B s L).2 = y)
    (hfin : (CubPlaneSet B x y).Finite) :
    T.ncard ≤ (CubPlaneSet B x y).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun L => Work.Q44Geom.ratSpan L) ?_ ?_ hfin
  · intro L hL
    obtain ⟨hLset, hx, hy⟩ := hT L hL
    have hspec := cubPair_spec hLset
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Work.Q44Geom.ratSpan_finrank_general, hLset.2.1]
    · rw [← hx]; exact Work.Q44Geom.toRatLM_mem_ratSpan hspec.1
    · rw [← hy]; exact Work.Q44Geom.toRatLM_mem_ratSpan hspec.2.1
    · intro z hz
      exact vanishRatSpanCub hB hLset.2.2.2 z hz
  · intro L₁ h1 L₂ h2 heq
    exact Work.Q44Geom.ratSpan_injective_of_isPrimLat (hT L₁ h1).1.1 (hT L₂ h2).1.1 heq

end Work.HP.MDEstimates
