import Mathlib
import Submission.Work.CFTLib.ContCohomology.Inhomogeneous
import Submission.Work.CFT.MaxProP.ContCohomology.Defs
import Submission.Work.CFT.MaxProP.ContCohomology.FiniteLevel.H2FpCont_finite
import Submission.Work.CFTLib.Topology.factorThroughFiniteQuotient
import Submission.Work.CFTLib.ContCohomology.ContinuousQuotient

namespace Work.CFTLib.ContCohomology

open CategoryTheory groupCohomology

/-- **Continuous `H²` of a profinite group with trivial `𝔽_p`-coefficients is the filtered colimit
of the `H²` of its finite quotients.**  Here `iComplex p` is the inhomogeneous complex of
continuous cochains `(Fin n → Γ) → 𝔽_p` and `Work.CFT.MaxProP.H2FpCont p Γ` is the filtered colimit
of the abstract group cohomology groups `H²(Γ ⧸ U, 𝔽_p)` over the open normal subgroups `U ▷ Γ`.
The iso is induced by the pullback of cocycles along `Γ → Γ ⧸ U`, using that a continuous cocycle
into the discrete module `𝔽_p` factors through such a quotient. -/
theorem iComplex_homology_two_iso_H2FpCont
    (p : ℕ) [Fact p.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] :
    Nonempty (↥((Work.CFTLib.ContCohomology.iComplex (Γ := Γ) p).homology 2) ≃ₗ[ZMod p]
      Work.CFT.MaxProP.H2FpCont p Γ) := by
  classical
  -- The cocone of the colimit: the pullback maps on `H²`.
  let hΦ : (U : Work.CFT.MaxProP.OpenNormal Γ) →
      Work.CFT.MaxProP.H2FpContFamily p Γ U →ₗ[ZMod p] iConc p Γ :=
    fun U => (pbConc p U).comp (H2ConcEquiv p (Γ ⧸ U.carrier)).toLinearMap
  have hnat : ∀ (U V : Work.CFT.MaxProP.OpenNormal Γ) (h : U ≤ V)
      (x : Work.CFT.MaxProP.H2FpContFamily p Γ U),
      hΦ V (Work.CFT.MaxProP.contMap p Γ U V h x) = hΦ U x := by
    intro U V h x
    refine groupCohomology.H2_induction_on x (C := fun y =>
      hΦ V (Work.CFT.MaxProP.contMap p Γ U V h y) = hΦ U y) ?_
    intro c
    change pbConc p V ((H2ConcEquiv p (Γ ⧸ V.carrier)).toLinearMap
        (Work.CFT.MaxProP.contMap p Γ U V h
          (groupCohomology.H2π (Aq p (Γ ⧸ U.carrier)) c)))
      = pbConc p U ((H2ConcEquiv p (Γ ⧸ U.carrier)).toLinearMap
          (groupCohomology.H2π (Aq p (Γ ⧸ U.carrier)) c))
    rw [show Work.CFT.MaxProP.contMap p Γ U V h = Work.CFT.KochTransfer.infl
        (Work.CFT.MaxProP.OpenNormal.quotientMap U V h) from rfl,
      Work.CFT.KochTransfer.infl_H2π]
    rw [show (H2ConcEquiv p (Γ ⧸ V.carrier)).toLinearMap
        (groupCohomology.H2π (Aq p (Γ ⧸ V.carrier))
          (Work.CFT.KochTransfer.precompCocycle
            (Work.CFT.MaxProP.OpenNormal.quotientMap U V h) c))
        = gQ p (Γ ⧸ V.carrier) (Work.CFT.KochTransfer.precompCocycle
            (Work.CFT.MaxProP.OpenNormal.quotientMap U V h) c) from
      (gQ_apply p _ _).symm]
    rw [show (H2ConcEquiv p (Γ ⧸ U.carrier)).toLinearMap
        (groupCohomology.H2π (Aq p (Γ ⧸ U.carrier)) c)
        = gQ p (Γ ⧸ U.carrier) c from (gQ_apply p _ _).symm]
    rw [pbConc_apply, pbConc_apply, pbZ_natural p h]
  -- Surjectivity of the canonical map.
  have hsurj : Function.Surjective (Work.CFT.MaxProP.H2FpCont.lift hΦ hnat) := by
    intro y
    obtain ⟨z, hz⟩ := piI_surjective (Γ := Γ) p y
    obtain ⟨U₀, F, hF⟩ := Work.CFTLib.Topology.factorThroughFiniteQuotient (M := ZMod p) 2
      ((z : ↥(iCochain (Γ := Γ) p 2)).1) ((z : ↥(iCochain (Γ := Γ) p 2)).2)
    let U : Work.CFT.MaxProP.OpenNormal Γ := ⟨U₀.toSubgroup, U₀.isNormal', U₀.isOpen'⟩
    let c : ((Γ ⧸ U.carrier) × (Γ ⧸ U.carrier)) → ZMod p := rx2 p (Γ ⧸ U.carrier) F
    have hc : c ∈ cocycles₂ (Aq p (Γ ⧸ U.carrier)) := by
      rw [← Work.CFT.KochTransfer.precompFun_mem_cocycles_iff (QuotientGroup.mk' U.carrier)
        (QuotientGroup.mk'_surjective U.carrier)]
      have hpre : Work.CFT.KochTransfer.precompFun (QuotientGroup.mk' U.carrier) c
          = rx2 p Γ ((z : ↥(iCochain (Γ := Γ) p 2)).1) := by
        funext x
        obtain ⟨g, h⟩ := x
        rw [Work.CFT.KochTransfer.precompFun_apply,
          show c = rx2 p (Γ ⧸ U.carrier) F from rfl, rx2_apply, rx2_apply]
        rw [hF (fun i : Fin 2 => if i = 0 then g else h)]
        congr 1
        funext i
        fin_cases i <;> rfl
      rw [hpre]
      rw [show cocycles₂ (Aq p Γ) = LinearMap.ker (d₂₃ (Aq p Γ)).hom from rfl,
        LinearMap.mem_ker]
      rw [show d₂₃ (Aq p Γ) (rx2 p Γ ((z : ↥(iCochain (Γ := Γ) p 2)).1))
          = (rx3 p Γ) ((inhomogeneousCochains (Aq p Γ)).d 2 3
              ((z : ↥(iCochain (Γ := Γ) p 2)).1)) from (d₂₃_comm p Γ _).symm]
      rw [iZ_d_zero p z, map_zero]
    have hcocycle : ∀ x : Fin 2 → Γ,
        ((pbZ p U ⟨c, hc⟩ : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1 x
          = (z : ↥(iCochain (Γ := Γ) p 2)).1 x := by
      intro x
      rw [pbZ_mk_apply, show c = rx2 p (Γ ⧸ U.carrier) F from rfl, rx2_apply, hF]
      congr 1
      funext i
      fin_cases i <;> rfl
    have hzz : pbZ p U ⟨c, hc⟩ = (show iK p Γ from z) := by
      apply Subtype.ext
      apply Subtype.ext
      funext x
      exact hcocycle x
    refine ⟨Work.CFT.MaxProP.H2FpCont.of p Γ U
      ((H2ConcEquiv p (Γ ⧸ U.carrier)).symm (gQ p (Γ ⧸ U.carrier) ⟨c, hc⟩)), ?_⟩
    rw [show (Work.CFT.MaxProP.H2FpCont.lift hΦ hnat)
        (Work.CFT.MaxProP.H2FpCont.of p Γ U
          ((H2ConcEquiv p (Γ ⧸ U.carrier)).symm (gQ p (Γ ⧸ U.carrier) ⟨c, hc⟩)))
        = hΦ U ((H2ConcEquiv p (Γ ⧸ U.carrier)).symm (gQ p (Γ ⧸ U.carrier) ⟨c, hc⟩)) from
      Work.CFT.MaxProP.H2FpCont.lift_of hΦ hnat U _]
    simp only [hΦ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, pbConc_apply, hzz, hz]
  -- Injectivity of the canonical map.
  have hinj : Function.Injective (Work.CFT.MaxProP.H2FpCont.lift hΦ hnat) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x
    refine Work.CFT.MaxProP.H2FpCont.induction_on x (C := fun y =>
      (Work.CFT.MaxProP.H2FpCont.lift hΦ hnat) y = 0 → y = 0) ?_
    intro U xU hx
    obtain ⟨c, hc⟩ : ∃ c : ↥(cocycles₂ (Aq p (Γ ⧸ U.carrier))),
        gQ p (Γ ⧸ U.carrier) c = (H2ConcEquiv p (Γ ⧸ U.carrier)) xU :=
      gQ_surjective p _ ((H2ConcEquiv p (Γ ⧸ U.carrier)) xU)
    have hx' : hΦ U xU = 0 := by
      rw [← Work.CFT.MaxProP.H2FpCont.lift_of hΦ hnat U xU]
      exact hx
    have hx'' : pbConc p U (gQ p (Γ ⧸ U.carrier) c) = 0 := by
      rw [hc]
      simpa only [hΦ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using hx'
    have hmem : ((pbZ p U c : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)) ∈ iB p Γ :=
      (piI_eq_zero_iff' p _).mp (by rw [← pbConc_apply]; exact hx'')
    rw [iB, LinearMap.mem_range] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨V₀, bV, hbV⟩ := Work.CFTLib.Topology.factorThroughFiniteQuotient (M := ZMod p) 1
      (b.1 : (Fin 1 → Γ) → ZMod p) b.2
    let V : Work.CFT.MaxProP.OpenNormal Γ := ⟨V₀.toSubgroup, V₀.isNormal', V₀.isOpen'⟩
    obtain ⟨W, hUW, hVW⟩ := exists_ge_ge U V
    let w : Γ ⧸ W.carrier → ZMod p := fun y =>
      bV (fun _ : Fin 1 => Work.CFT.MaxProP.OpenNormal.quotientMap V W hVW y)
    have hbW : b.1 = pull1 (Γ := Γ) p (QuotientGroup.mk' W.carrier) w :=
      pull1_eq_of_factor p hVW bV b hbV
    let cW : ↥(cocycles₂ (Aq p (Γ ⧸ W.carrier))) :=
      Work.CFT.KochTransfer.precompCocycle (Work.CFT.MaxProP.OpenNormal.quotientMap U W hUW) c
    -- the underlying functions of `iDiff p 1 b` and `pbZ p W cW` agree
    have hfun : d₁₂ (Aq p (Γ ⧸ W.carrier)) w
        = (cW : ((Γ ⧸ W.carrier) × (Γ ⧸ W.carrier)) → ZMod p) := by
      refine Work.CFT.KochTransfer.precompFun_injective (QuotientGroup.mk' W.carrier)
        (QuotientGroup.mk'_surjective W.carrier) ?_
      rw [precompFun_d₁₂]
      rw [show Work.CFT.KochTransfer.precompFun (QuotientGroup.mk' W.carrier)
          (cW : ((Γ ⧸ W.carrier) × (Γ ⧸ W.carrier)) → ZMod p)
          = (rx2 p Γ) (pull2 (Γ := Γ) p (QuotientGroup.mk' W.carrier)
              (cW : ((Γ ⧸ W.carrier) × (Γ ⧸ W.carrier)) → ZMod p)) from rfl]
      rw [d₁₂_eq_rx2]
      congr 1
      rw [show (rx1 p Γ).symm (precompFun1 p (QuotientGroup.mk' W.carrier) w)
          = pull1 (Γ := Γ) p (QuotientGroup.mk' W.carrier) w from rfl, ← hbW]
      rw [show pull2 (Γ := Γ) p (QuotientGroup.mk' W.carrier)
          (cW : ((Γ ⧸ W.carrier) × (Γ ⧸ W.carrier)) → ZMod p)
          = ((pbZ p W cW : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1 from rfl]
      rw [show ((pbZ p W cW : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1
          = ((pbZ p U c : iK p Γ) : ↥(iCochain (Γ := Γ) p 2)).1 from by
        rw [pbZ_natural p hUW]]
      rw [← iDiff_eq_d', hb]
    have hker : gQ p (Γ ⧸ W.carrier) cW = 0 := by
      rw [show gQ p (Γ ⧸ W.carrier) cW
          = H2ConcEquiv p (Γ ⧸ W.carrier)
              (groupCohomology.H2π (Aq p (Γ ⧸ W.carrier)) cW) from rfl]
      rw [show groupCohomology.H2π (Aq p (Γ ⧸ W.carrier)) cW = 0 from
        (groupCohomology.H2π_eq_zero_iff (A := Aq p (Γ ⧸ W.carrier)) cW).mpr
          (by rw [← hfun]; exact LinearMap.mem_range_self _ _)]
      rw [map_zero]
    have hfinal : Work.CFT.MaxProP.H2FpCont.of p Γ U xU = 0 := by
      rw [show xU = (H2ConcEquiv p (Γ ⧸ U.carrier)).symm (gQ p (Γ ⧸ U.carrier) c) from by
        rw [hc, LinearEquiv.symm_apply_apply]]
      rw [← Work.CFT.MaxProP.H2FpCont.of_f (p := p) (G := Γ) hUW
        ((H2ConcEquiv p (Γ ⧸ U.carrier)).symm (gQ p (Γ ⧸ U.carrier) c))]
      rw [contMap_H2ConcEquiv_symm p hUW c]
      rw [show (H2ConcEquiv p (Γ ⧸ W.carrier)).symm (gQ p (Γ ⧸ W.carrier) cW)
          = groupCohomology.H2π (Aq p (Γ ⧸ W.carrier)) cW from by
        rw [gQ_apply, LinearEquiv.symm_apply_apply]]
      rw [show groupCohomology.H2π (Aq p (Γ ⧸ W.carrier)) cW = 0 from
        (H2ConcEquiv p (Γ ⧸ W.carrier)).injective (by rw [← gQ_apply, hker, map_zero])]
      rw [map_zero]
    exact hfinal
  exact ⟨(iConcEquiv (Γ := Γ) p).trans
    (LinearEquiv.ofBijective (Work.CFT.MaxProP.H2FpCont.lift hΦ hnat)
      ⟨hinj, hsurj⟩).symm⟩

end Work.CFTLib.ContCohomology
