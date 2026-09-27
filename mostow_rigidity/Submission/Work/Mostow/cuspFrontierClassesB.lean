import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp
import Submission.Work.Mostow.thickPart_cocompact
import Submission.Work.Mostow.cuspHoro.packingCount
import Submission.Work.Mostow.VolDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- **Packing bound.**  A subset of a compact set which is separated by a positive constant with
respect to a continuous symmetric "distance" satisfying the triangle inequality and vanishing on
the diagonal is finite.  This is the packing step of the Margulis argument: a `c`-separated subset
of a compact set is finite. -/
lemma finite_of_separated_subset_compact {α : Type*} [TopologicalSpace α]
    {d : α → α → ℝ} (hdrefl : ∀ x, d x x = 0) (hdsymm : ∀ x y, d x y = d y x)
    (hdtri : ∀ x y z, d x z ≤ d x y + d y z)
    (hdcont : Continuous (fun p : α × α => d p.1 p.2))
    {K T : Set α} (hK : IsCompact K) (hTK : T ⊆ K) {c : ℝ} (hc : 0 < c)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → c < d x y) : T.Finite := by
  classical
  -- cover `K` by the open sets `{v | d x v < c/2}`, `x ∈ K`
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => {v : α | d x.1 v < c / 2})
    (fun x => isOpen_lt (hdcont.comp (continuous_const.prodMk continuous_id)) continuous_const)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by
      show d x x < c / 2
      rw [hdrefl]; linarith⟩)
  -- each of these sets meets `T` in at most one point
  have hsub : T ⊆ ⋃ i ∈ (t : Set K), {v : α | d i.1 v < c / 2} ∩ T := by
    intro x hx
    have h1 : x ∈ ⋃ i ∈ (t : Set K), {v : α | d i.1 v < c / 2} := ht (hTK hx)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_inter_iff] at h1 ⊢
    obtain ⟨i, hi, h2⟩ := h1
    exact ⟨i, hi, h2, hx⟩
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion t.finite_toSet (fun i _ => Set.Subsingleton.finite ?_)
  intro x hx y hy
  by_contra hne
  have h1 : c < d x y := hsep x hx.2 y hy.2 hne
  have h2 : d x y < c := by
    have h3 : d i.1 x < c / 2 := hx.1
    have h4 : d i.1 y < c / 2 := hy.1
    have h5 : d x i.1 = d i.1 x := hdsymm _ _
    have h6 : d x y ≤ d x i.1 + d i.1 y := hdtri _ _ _
    linarith
  linarith

theorem cuspFrontierClassesB (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {εsep : ℝ} (hεseppos : 0 < εsep)
    (hsep : ∀ η ∈ Work.Mostow.parFixed Γ, ∀ η' ∈ Work.Mostow.parFixed Γ, η ≠ η' →
      Disjoint (Work.Mostow.cuspThinRegion Γ η εsep)
        (Work.Mostow.cuspThinRegion Γ η' εsep))
    {εB : ℝ} (hεB : 0 < εB) {r : ℝ} (hr : 0 < r)
    (hball : ∀ η ∈ Work.Mostow.parFixed Γ, ∀ ε : ℝ, 0 < ε → ε ≤ εB →
      ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) = Work.Mostow.cEps ε →
      ∀ w : Submission.Mostow.E n, Submission.Mostow.hdist u w ≤ r * ε →
        w ∈ Work.Mostow.cuspThinRegion Γ η (2 * ε))
    {ε : ℝ} (hε : 0 < ε) (hεB' : ε ≤ εB) (h2ε : 2 * ε ≤ εsep)
    (heq : ∀ η ∈ Work.Mostow.parFixed Γ, ∀ u : Submission.Mostow.E n,
      u ∈ frontier (Work.Mostow.cuspThinRegion Γ η ε) →
      Work.Mostow.lev η u * Work.Mostow.parDisp Γ η (Work.Mostow.yc η u) = Work.Mostow.cEps ε)
    {K : Set (Submission.Mostow.E n)} (hK : IsCompact K) :
    {η : Submission.Mostow.E n | η ∈ Work.Mostow.parFixed Γ ∧
      (frontier (Work.Mostow.cuspThinRegion Γ η ε) ∩ K).Nonempty}.Finite := by
  classical
  -- the metric facts about `hdist`
  have hdrefl : ∀ u : E n, hdist u u = 0 := fun u => (hI.2.2.1 u u).mpr rfl
  have hdsymm : ∀ u v : E n, hdist u v = hdist v u := hI.2.1
  have hdtri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w := hI.2.2.2.1
  have hdcont : Continuous (fun p : E n × E n => hdist p.1 p.2) := hI.2.2.2.2.1
  -- the set whose finiteness is the goal
  set S : Set (E n) := {η : E n | η ∈ parFixed Γ ∧
    (frontier (cuspThinRegion Γ η ε) ∩ K).Nonempty} with hSdef
  -- choose, for each `η ∈ S`, a point of the frontier of its thin region inside `K`
  let f : E n → E n := fun η => if h : η ∈ S then Classical.choose h.2 else 0
  have hf_eq : ∀ (η : E n) (hη : η ∈ S), f η = Classical.choose hη.2 := by
    intro η hη
    dsimp only [f]
    rw [dif_pos hη]
  have hfwit : ∀ (η : E n) (hη : η ∈ S),
      f η ∈ frontier (cuspThinRegion Γ η ε) ∩ K := by
    intro η hη
    rw [hf_eq η hη]
    exact Classical.choose_spec hη.2
  -- distinct cusps give points at hyperbolic distance more than `r * ε`
  have hfsep : ∀ (η : E n) (hη : η ∈ S) (η' : E n) (hη' : η' ∈ S), η ≠ η' →
      r * ε < hdist (f η) (f η') := by
    intro η hη η' hη' hne
    by_contra hcon
    push_neg at hcon
    have hηP : η ∈ parFixed Γ := hη.1
    have hη'P : η' ∈ parFixed Γ := hη'.1
    have heqη : lev η (f η) * parDisp Γ η (yc η (f η)) = cEps ε :=
      heq η hηP (f η) (hfwit η hη).1
    have heqη' : lev η' (f η') * parDisp Γ η' (yc η' (f η')) = cEps ε :=
      heq η' hη'P (f η') (hfwit η' hη').1
    -- the ball around `f η'` lies in the thin region at `η` of level `2ε`
    have h1 : f η' ∈ cuspThinRegion Γ η (2 * ε) :=
      hball η hηP ε hε hεB' (f η) heqη (f η') hcon
    have h0 : hdist (f η') (f η') ≤ r * ε := by
      rw [hdrefl (f η')]; exact le_of_lt (mul_pos hr hε)
    have h2 : f η' ∈ cuspThinRegion Γ η' (2 * ε) :=
      hball η' hη'P ε hε hεB' (f η') heqη' (f η') h0
    exact Set.disjoint_left.mp (hsep η hηP η' hη'P hne)
      (cuspThinRegion_mono h2ε h1) (cuspThinRegion_mono h2ε h2)
  -- the image of `f` is a separated subset of the compact set `K`
  have hTfin : (f '' S).Finite := by
    refine finite_of_separated_subset_compact (d := hdist) (K := K) (T := f '' S)
      (c := r * ε) hdrefl hdsymm hdtri hdcont hK ?_ (mul_pos hr hε) ?_
    · rintro u ⟨η, hη, rfl⟩
      exact (hfwit η hη).2
    · rintro u ⟨η, hη, rfl⟩ u' ⟨η', hη', rfl⟩ hne
      exact hfsep η hη η' hη' (fun h => hne (congrArg f h))
  -- `f` is injective on `S`, so `S` is finite
  refine Set.Finite.of_finite_image hTfin ?_
  intro η hη η' hη' hff
  by_contra hne
  have h1 := hfsep η hη η' hη' hne
  have hz : hdist (f η) (f η') = 0 := by rw [hff, hdrefl]
  rw [hz] at h1
  exact absurd h1 (not_lt.mpr (le_of_lt (mul_pos hr hε)))

end Work.Mostow
