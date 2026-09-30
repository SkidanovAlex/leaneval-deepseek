import Mathlib
import Submission.Work.SSS.serreE1PieceDefs
import Submission.Work.Serre.serreE2a
import Submission.Work.Serre.sHatExtend

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-- **The relative HLP of a Serre fibration for the simplex hat.**  Let
`sHat n = (Δⁿ × {0}) ∪ (∂Δⁿ × I) ⊆ Δⁿ × I` be the hat of the simplex-cylinder (the "bottom plus
lateral boundary"), and `sHatIncl n : sHat n ⟶ Δⁿ × I` its inclusion.  For a Serre fibration
`p : E → B`, a homotopy `H : Δⁿ × I → B` and a lift `g` of `H|_{sHat n}` along `p`, there is an
extension `G : Δⁿ × I → E` of `g` lifting `H`.

This is the simplex analogue of `Work.Serre.SerreE2a` (the relative cube HLP
`Work.StemsB.HasHLPRel`, with the prescribed data on `Iⁿ × {0} ∪ ∂Iⁿ × I`); it is obtained by
transporting along the collapse `collapseProj n : Iⁿ × I ⟶ Δⁿ × I` of `Work.Serre.sHatExtend`
(a closed quotient map whose non-trivial fibres lie in the hat, and along which everything
descends). -/
theorem exists_lift_sHat {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (n : ℕ)
    (H : C(↥(stdSimplex ℝ (Fin (n+1))) × unitInterval, B))
    (g : C(↥(Work.Serre.sHat n), E))
    (hg : p.comp g = H.comp (Work.SSS.sHatIncl n)) :
    ∃ G : C(↥(stdSimplex ℝ (Fin (n+1))) × unitInterval, E),
      p.comp G = H ∧ ∀ x : ↥(Work.Serre.sHat n), G (Work.SSS.sHatIncl n x) = g x := by
  classical
  have hsurj : Function.Surjective (Work.Serre.collapseProj n) := by
    intro q
    refine ⟨(Work.Serre.simplexPreimage n q.1, q.2), ?_⟩
    change ((Work.RatHurewicz.H n) (Work.Serre.simplexPreimage n q.1), q.2) = q
    exact Prod.ext (Work.Serre.collapse_simplexPreimage n q.1) rfl
  have hcont : Continuous (Work.Serre.collapseProj n) := (Work.Serre.collapseProj n).continuous
  have hquot : Topology.IsQuotientMap (Work.Serre.collapseProj n) :=
    (Continuous.isClosedMap hcont).isQuotientMap hcont hsurj
  have hmap : ∀ q : ↥(Work.Serre.hatSet n),
      Work.Serre.collapseProj n (q : Work.Stems.Cubical.IC n × unitInterval)
        ∈ Work.Serre.sHat n :=
    fun q => Work.Serre.mem_sHat_of_LSet q.1.1 q.1.2 q.2
  let ψ : C(↥(Work.Serre.hatSet n), ↥(Work.Serre.sHat n)) :=
    ⟨fun q => ⟨Work.Serre.collapseProj n (q : Work.Stems.Cubical.IC n × unitInterval), hmap q⟩,
      Continuous.subtype_mk (hcont.comp continuous_subtype_val) _⟩
  let g' : C(↥(Work.Serre.hatSet n), E) := g.comp ψ
  have hg' : p.comp g' = (H.comp (Work.Serre.collapseProj n)).comp (Work.Serre.hatIncl n) := by
    ext q
    have h1 := congrFun (congrArg DFunLike.coe hg) (ψ q)
    rw [ContinuousMap.comp_apply] at h1
    show p (g (ψ q)) = H ((Work.SSS.sHatIncl n) (ψ q))
    exact h1
  obtain ⟨G', hG'p, hG'g⟩ :=
    Work.Serre.serreE2a E B p n hp (H.comp (Work.Serre.collapseProj n)) g' hg'
  have hG'_hat : ∀ (q : Work.Stems.Cubical.IC n × unitInterval)
      (hq : q ∈ Work.Serre.hatSet n), G' q = g' ⟨q, hq⟩ := by
    intro q hq
    exact hG'g ⟨q, hq⟩
  have hfac : Function.FactorsThrough (⇑G') (⇑(Work.Serre.collapseProj n)) := by
    intro a b hab
    have h1 : Work.RatHurewicz.H n a.1 = Work.RatHurewicz.H n b.1 := by
      have := congrArg Prod.fst hab
      simpa only [Work.Serre.collapseProj_apply] using this
    have h2 : a.2 = b.2 := by
      have := congrArg Prod.snd hab
      simpa only [Work.Serre.collapseProj_apply] using this
    rcases Work.RatHurewicz.Bridge.H_eq_or_boundary n h1 with heq | ⟨hb1, hb2⟩
    · exact congrArg G' (Prod.ext heq h2)
    · have ha : a ∈ Work.Serre.hatSet n := Or.inr hb1
      have hb : b ∈ Work.Serre.hatSet n := Or.inr hb2
      calc G' a = g' ⟨a, ha⟩ := hG'_hat a ha
        _ = g (ψ ⟨a, ha⟩) := rfl
        _ = g (ψ ⟨b, hb⟩) := congrArg g (Subtype.ext hab)
        _ = g' ⟨b, hb⟩ := rfl
        _ = G' b := (hG'_hat b hb).symm
  let F : C(↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval, E) := hquot.lift G' hfac
  have hFcomp : F.comp (Work.Serre.collapseProj n) = G' := hquot.lift_comp G' hfac
  refine ⟨F, ?_, ?_⟩
  · ext q
    obtain ⟨y, hy⟩ := hsurj q
    have hFy : F q = G' y := by
      have h := congrFun (congrArg DFunLike.coe hFcomp) y
      rw [ContinuousMap.comp_apply] at h
      rw [← hy]
      exact h
    have hGy : p (G' y) = H (Work.Serre.collapseProj n y) :=
      congrFun (congrArg DFunLike.coe hG'p) y
    rw [ContinuousMap.comp_apply, hFy, hGy, hy]
  · intro x
    have hΦy : Work.Serre.collapseProj n
        (Work.Serre.simplexPreimage n x.1.1, x.1.2) = x.1 := by
      change ((Work.RatHurewicz.H n) (Work.Serre.simplexPreimage n x.1.1), x.1.2) = x.1
      exact Prod.ext (Work.Serre.collapse_simplexPreimage n x.1.1) rfl
    have hFx : F x.1 = G' (Work.Serre.simplexPreimage n x.1.1, x.1.2) := by
      have h := congrFun (congrArg DFunLike.coe hFcomp)
        (Work.Serre.simplexPreimage n x.1.1, x.1.2)
      rw [ContinuousMap.comp_apply] at h
      rw [hΦy] at h
      exact h
    have hmem : (Work.Serre.simplexPreimage n x.1.1, x.1.2) ∈ Work.Serre.hatSet n := by
      rcases x.2 with h0 | hb
      · exact Or.inl h0
      · refine Or.inr ?_
        obtain ⟨j, hj⟩ := hb
        exact Work.RatHurewicz.Bridge.Hfun_zero_mem_boundary _
          ⟨j, by
            rw [← Work.RatHurewicz.H_apply, Work.Serre.collapse_simplexPreimage n x.1.1]
            exact hj⟩
    have hfin : G' (Work.Serre.simplexPreimage n x.1.1, x.1.2) = g x := by
      rw [hG'_hat (Work.Serre.simplexPreimage n x.1.1, x.1.2) hmem]
      show g (ψ ⟨(Work.Serre.simplexPreimage n x.1.1, x.1.2), hmem⟩) = g x
      refine congrArg g (Subtype.ext ?_)
      change Work.Serre.collapseProj n (Work.Serre.simplexPreimage n x.1.1, x.1.2) = x.1
      exact hΦy
    rw [sHatIncl_apply, hFx, hfin]

end Work.SSS
