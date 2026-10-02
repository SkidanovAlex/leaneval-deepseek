import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre
import Submission.Work.ELAssembly.Q_adm_of
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.ELTop.RegionBasics
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.mem_polyRegion_iff_of_notMem_K
import Submission.Work.ELPull.isCoveringMapOn_tsqIterate
import Submission.Work.ELPull.critValues_tsqIterate
import Submission.Work.ELTop.isClosed_polyCurve
import Submission.Work.ELTop.frontier_polyRegion_inter_K
import Submission.Work.TopJordan.Jordan
import Submission.Work.ELNest.Qlev_facts
import Submission.Work.ELAssembly.pot_iterate
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.Top.extAngle_rayPt
import Submission.Work.Top.extAngle_of_mem_paramRay
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELNest.Qnest_shrinks
import Submission.Work.ELAssembly.pullQ_P0_eq
import Submission.Work.ELAssembly.pullQ_pair
import Submission.Work.ELAssembly.pullQ_fib
import Submission.Work.ELAssembly.base_shift_of
import Submission.Work.ELTop.polyRegion_eq_sides_I
import Submission.Work.ELTop.pairSides_decomposition

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Classical Filter Set
open scoped Topology

set_option maxHeartbeats 8000000


/-- The parameter ray of angle `θ` depends on `θ` only modulo `1`. -/
theorem paramRay_fract {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    Work.EL.paramRay hN (Int.fract θ) = Work.EL.paramRay hN θ := by
  have h := Work.ELTop.paramRay_add_int_aux hN (Int.fract θ) ⌊θ⌋
  rw [Int.fract_add_floor] at h
  exact h.symm

/-- **No point of the level-`(n+1)` region maps to a boundary ray of the level-`n` polygon.**
If `z ∈ U` and `F c z` lies on the ray of angle `P.a` for a pair `P` of the level-`n` polygon,
then the external angle `α` of `z` avoids the closed far arcs of the level-`(n+1)` polygon
(region description), while `T^[10] α ≡ P.a` (since `F` multiplies external angles by
`1024 = 2^10` on the escaping set); the contrapositive of the near-arc condition `I.arc` gives
`α ∈ [P'.a, P'.b]` for some pair `P'` of the level-`(n+1)` polygon, a contradiction. -/
theorem pullQ_notMem_paramRay {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ}
    {P0 : Work.EL.CoPair d.hN} {N : NestPairs d} (I : QPullInputs c d L P0 N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) (n : ℕ)
    {P : Work.EL.CoPair d.hN} (hP : P ∈ [P0, N.Qp n]) {z : ℂ}
    (hz : z ∈ Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))) :
    Work.EL.F c z ∉ Work.EL.paramRay d.hN P.a := by
  intro hmem
  have hR' : 1 < Work.ELNest.Qlev L (n + 1) := (Work.ELNest.Qlev_facts I.hL (n + 1)).1
  have hC' := Work.ELTop.polyCurve_isJordan d.hN [P0, N.Qp (n + 1)] (hadm (n + 1)) hR'
  have hzK : z ∉ Work.EL.K c := by
    intro hK
    have hFzK : Work.EL.F c z ∈ Work.EL.K c := Work.ELNest.mapsTo_F_K c hK
    exact (Work.EL.paramRay_subset_compl d.hN P.a) hmem hFzK
  set α : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z with hα
  have harcs : ∀ Q ∈ [P0, N.Qp (n + 1)], ¬ Work.EL.InClosedArc α Q.a Q.b :=
    ((Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN
      Work.TopJordan.jordanForm [P0, N.Qp (n + 1)] (hadm (n + 1)) hR' hC' hzK).mp hz).1
  have hzeq : Work.EL.rayPt d.hN α (Real.exp (Work.EL.pot d.hN z)) = z := by
    rw [hα]; exact Work.ELTop.rayPt_extAngle_exp_pot d.hN hzK
  have ht : 1 < Real.exp (Work.EL.pot d.hN z) := Work.ELTop.one_lt_exp_pot d.hN hzK
  set s : ℝ := (Real.exp (Work.EL.pot d.hN z)) ^ 1024 with hs
  have hs1 : 1 < s := by rw [hs]; exact one_lt_pow₀ ht (by norm_num)
  -- `F z = rayPt (T^[10] α) s`
  have hFz : Work.EL.F c z = Work.EL.rayPt d.hN (Work.EL.T^[10] α) s := by
    rw [Work.ELAssembly.EL_F_eq_tantibar, ← hzeq, hs]
    have h := Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher (θ := α)
      (t := Real.exp (Work.EL.pot d.hN z)) ht 10
    simpa using h
  -- the external angle of `F z` is `fract (T^[10] α)`
  have hray : Work.EL.rayPt d.hN (Work.EL.T^[10] α) s
      = Work.EL.rayPt d.hN (Int.fract (Work.EL.T^[10] α)) s := by
    have h := Work.ELTop.rayPt_add_int d.hN (Int.fract (Work.EL.T^[10] α)) s ⌊Work.EL.T^[10] α⌋
    rwa [Int.fract_add_floor] at h
  have hangle1 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (Work.EL.F c z)
      = Int.fract (Work.EL.T^[10] α) := by
    rw [hFz, hray]
    exact Work.Top.extAngle_rayPt d.hN (Int.fract_nonneg _) (Int.fract_lt_one _) hs1
  -- and it is `fract P.a`, since `F z` lies on the ray of angle `P.a`
  have hangle2 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (Work.EL.F c z)
      = Int.fract P.a := by
    have hp : Work.EL.F c z ∈ Work.EL.paramRay d.hN (Int.fract P.a) := by
      rw [paramRay_fract d.hN P.a]; exact hmem
    exact Work.Top.extAngle_of_mem_paramRay d.hN (Int.fract_nonneg P.a) (Int.fract_lt_one P.a) hp
  have hcong : ∃ k : ℤ, Work.EL.T^[10] α = P.a + k := by
    have hf : Int.fract (Work.EL.T^[10] α) = Int.fract P.a := hangle1.symm.trans hangle2
    obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp hf
    exact ⟨k, by linarith⟩
  have hInC : Work.EL.InClosedArc (Work.EL.T^[10] α) P.a P.b := by
    obtain ⟨k, hk⟩ := hcong
    have hf0 : Int.fract (Work.EL.T^[10] α - P.a) = 0 := by
      rw [hk, show P.a + (k : ℝ) - P.a = (k : ℝ) by ring, Int.fract_intCast]
    exact ⟨le_of_eq hf0.symm, by rw [hf0]; exact Work.EL.arcLen_nonneg P.a P.b⟩
  exact (I.arc n α harcs P hP) hInC


/-! ## Elementary angle/level infrastructure for the pull-back -/

/-- `InClosedArc` is insensitive to shifting the angle by an integer. -/
theorem InClosedArc_add_int_iff (θ a b : ℝ) (k : ℤ) :
    Work.EL.InClosedArc (θ + (k : ℝ)) a b ↔ Work.EL.InClosedArc θ a b := by
  unfold Work.EL.InClosedArc Work.EL.arcLen
  have h : θ + (k : ℝ) - a = (θ - a) + (k : ℝ) := by ring
  rw [h, Int.fract_add_intCast]

/-- `(Qlev L (n+1)) ^ 1024 = Qlev L n` for `1 < L`. -/
theorem Qlev_succ_pow {L : ℝ} (hL : 1 < L) (n : ℕ) :
    (Work.ELNest.Qlev L (n + 1)) ^ 1024 = Work.ELNest.Qlev L n := by
  have hL0 : (0 : ℝ) ≤ L := le_of_lt (lt_trans zero_lt_one hL)
  have hpow : (1024 : ℝ) ^ (n + 1) = (1024 : ℝ) ^ n * 1024 := by rw [pow_succ]
  have hne : ((1024 : ℝ) ^ n) ≠ 0 := by positivity
  rw [Work.ELNest.Qlev, Work.ELNest.Qlev, ← Real.rpow_natCast, ← Real.rpow_mul hL0]
  have hexp : (1 : ℝ) / (1024 : ℝ) ^ (n + 1) * ((1024 : ℕ) : ℝ) = 1 / (1024 : ℝ) ^ n := by
    rw [Nat.cast_ofNat, hpow]
    have h1 : (1024 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
  rw [hexp]

/-- `1 < Real.sqrt R` for `1 < R`. -/
theorem one_lt_sqrt {R : ℝ} (hR : 1 < R) : 1 < Real.sqrt R := by
  have h := (Real.lt_sqrt (x := 1) (y := R) zero_le_one).mpr (by simpa using hR)
  simpa using h

/-- `Work.EL.F c` is continuous. -/
theorem continuous_F (c : ℂ) : Continuous (Work.EL.F c) := by
  have hTsq : Continuous (Work.Landing.Tsq c) := by
    rw [show Work.Landing.Tsq c = fun z : ℂ => (z ^ 2 + star c) ^ 2 + c from
      funext (Work.Landing.Tsq_apply c)]
    fun_prop
  simpa [Work.EL.F] using hTsq.iterate 5

/-- `Work.EL.F c` is an open map (a non-constant polynomial). -/
theorem isOpenMap_F (c : ℂ) : IsOpenMap (Work.EL.F c) := by
  have hsq : IsOpenMap (fun z : ℂ => z ^ 2) := (Complex.isOpenQuotientMap_pow 2).isOpenMap
  have hTsq : IsOpenMap (Work.Landing.Tsq c) := by
    rw [show Work.Landing.Tsq c
        = (fun z : ℂ => z + c) ∘ (fun z : ℂ => z ^ 2) ∘ (fun z : ℂ => z + star c)
            ∘ (fun z : ℂ => z ^ 2) from funext (fun z => by
              rw [Work.Landing.Tsq_apply]; simp [Function.comp])]
    exact (isOpenMap_add_right c).comp (hsq.comp ((isOpenMap_add_right (star c)).comp hsq))
  have hiter : ∀ m : ℕ, IsOpenMap ((Work.Landing.Tsq c)^[m]) := by
    intro m
    induction m with
    | zero => simpa using (IsOpenMap.id : IsOpenMap (id : ℂ → ℂ))
    | succ m ih => rw [Function.iterate_succ']; exact hTsq.comp ih
  simpa [Work.EL.F] using hiter 5

/-- **Local surjectivity of `F c`**: around any point, `F c` maps balls onto neighbourhoods of
the image point (the open mapping theorem for a non-constant polynomial). -/
theorem exists_preimage_near (c : ℂ) (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, ‖y - Work.EL.F c x‖ < δ →
      ∃ z : ℂ, ‖z - x‖ < ε ∧ Work.EL.F c z = y := by
  have himg : Work.EL.F c '' Metric.ball x ε ∈ 𝓝 (Work.EL.F c x) :=
    (isOpenMap_F c).image_mem_nhds (Metric.ball_mem_nhds x hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨δ, hδ, fun y hy => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hsub (by rwa [Metric.mem_ball, dist_eq_norm])
  exact ⟨z, by rwa [Metric.mem_ball, dist_eq_norm] at hz, hzy⟩

/-- `F c` maps the level-`(n+1)` region into the level-`n` region. -/
theorem pullQ_map {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) (n : ℕ) :
    Set.MapsTo (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)))
      (Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n)) := by
  have hL := I.hL
  have hR' : 1 < Work.ELNest.Qlev L (n + 1) := (Work.ELNest.Qlev_facts hL (n + 1)).1
  have hR : 1 < Work.ELNest.Qlev L n := (Work.ELNest.Qlev_facts hL n).1
  have hpow := Qlev_succ_pow hL n
  have hJ := Work.TopJordan.jordanForm
  have hAdm' : Work.EL.PolyAdmissible [P0, N.Qp (n + 1)] := hadm (n + 1)
  have hAdm : Work.EL.PolyAdmissible [P0, N.Qp n] := hadm n
  have hC' := Work.ELTop.polyCurve_isJordan d.hN [P0, N.Qp (n + 1)] hAdm' hR'
  have hC := Work.ELTop.polyCurve_isJordan d.hN [P0, N.Qp n] hAdm hR
  -- ## the non-`K` part
  have hnonK : ∀ z ∈ Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)),
      z ∉ Work.EL.K c → Work.EL.F c z ∈ Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n) := by
    intro z hz hzK
    obtain ⟨harcs, hpot⟩ := (Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN hJ
      [P0, N.Qp (n + 1)] hAdm' hR' hC' hzK).mp hz
    set α : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z with hα
    have hzeq : Work.EL.rayPt d.hN α (Real.exp (Work.EL.pot d.hN z)) = z := by
      rw [hα]; exact Work.ELTop.rayPt_extAngle_exp_pot d.hN hzK
    have ht : 1 < Real.exp (Work.EL.pot d.hN z) := Work.ELTop.one_lt_exp_pot d.hN hzK
    set s : ℝ := (Real.exp (Work.EL.pot d.hN z)) ^ 1024 with hs
    have hs1 : 1 < s := by rw [hs]; exact one_lt_pow₀ ht (by norm_num)
    have hFz : Work.EL.F c z = Work.EL.rayPt d.hN (Work.EL.T^[10] α) s := by
      rw [Work.ELAssembly.EL_F_eq_tantibar, ← hzeq, hs]
      have h := Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher (θ := α)
        (t := Real.exp (Work.EL.pot d.hN z)) ht 10
      simpa using h
    have hray : Work.EL.rayPt d.hN (Work.EL.T^[10] α) s
        = Work.EL.rayPt d.hN (Int.fract (Work.EL.T^[10] α)) s := by
      have h := Work.ELTop.rayPt_add_int d.hN (Int.fract (Work.EL.T^[10] α)) s
        ⌊Work.EL.T^[10] α⌋
      rwa [Int.fract_add_floor] at h
    have hext : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (Work.EL.F c z)
        = Int.fract (Work.EL.T^[10] α) := by
      rw [hFz, hray]
      exact Work.Top.extAngle_rayPt d.hN (Int.fract_nonneg _) (Int.fract_lt_one _) hs1
    have hFzK : Work.EL.F c z ∉ Work.EL.K c := by
      rw [hFz]; exact Work.EL.rayPt_notMem_K d.hN hs1
    rw [Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN hJ [P0, N.Qp n] hAdm hR hC hFzK]
    refine ⟨?_, ?_⟩
    · intro P hP
      rw [hext]
      intro hcon
      exact (I.arc n α harcs P hP) (by
        have h := (InClosedArc_add_int_iff (Int.fract (Work.EL.T^[10] α)) P.a P.b
          ⌊Work.EL.T^[10] α⌋).mpr hcon
        rwa [Int.fract_add_floor] at h)
    · have hpotF : Work.EL.pot d.hN (Work.EL.F c z) = 1024 * Work.EL.pot d.hN z := by
        rw [Work.ELAssembly.EL_F_eq_tantibar]
        have h := Work.ELAssembly.pot_iterate d 10 z
        norm_num at h ⊢
        exact h
      have hlog : Real.log (Work.ELNest.Qlev L n)
          = 1024 * Real.log (Work.ELNest.Qlev L (n + 1)) := by
        rw [← hpow, Real.log_pow]; norm_num
      rw [hpotF, hlog]
      have hlp := Real.log_pos hR'
      nlinarith [hpot, hlp]
  -- ## the `K` part: `F` sends no point of `U ∩ K` onto the boundary
  have hKpart : ∀ z ∈ Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)),
      z ∈ Work.EL.K c →
      Work.EL.F c z ∉ Work.EL.polyCurve [P0, N.Qp n] (Work.ELNest.Qlev L n) := by
    intro z hz hzK hFzC
    have hFzK : Work.EL.F c z ∈ Work.EL.K c :=
      Work.ELNest.mapsTo_F_K c hzK
    have hinter := Work.ELTop.polyCurve_inter_K d.hN [P0, N.Qp n] hR
    have hmem : Work.EL.F c z ∈ Work.EL.polyCurve [P0, N.Qp n] (Work.ELNest.Qlev L n)
        ∩ Work.EL.K c := ⟨hFzC, hFzK⟩
    rw [hinter] at hmem
    obtain ⟨P, hP, hPy⟩ := hmem
    -- a small ball around `z` inside `U`
    have hUo : IsOpen (Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))) :=
      Work.ELTop.isOpen_polyRegion d.hN _ _ (Work.ELTop.isClosed_polyCurve d.hN _ _)
    obtain ⟨ε, hε0, hεU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hz)
    obtain ⟨δ, hδ0, hδ⟩ := exists_preimage_near c z hε0
    -- the ray of `P` approaches `F c z`; pick a level with `rayPt` close to it
    have hlands : Tendsto (fun t : ℝ => Work.EL.rayPt d.hN P.a t)
        (nhdsWithin (1:ℝ) (Set.Ioi 1)) (𝓝 (Work.EL.F c z)) := hPy ▸ P.lands_a
    have hev : ∀ᶠ t : ℝ in nhdsWithin (1:ℝ) (Set.Ioi 1),
        Work.EL.rayPt d.hN P.a t ∈ Metric.ball (Work.EL.F c z) δ :=
      hlands (Metric.ball_mem_nhds (Work.EL.F c z) hδ0)
    have hIoi : ∀ᶠ t : ℝ in nhdsWithin (1:ℝ) (Set.Ioi 1), t ∈ Set.Ioi (1:ℝ) :=
      self_mem_nhdsWithin
    obtain ⟨t, htball, htIoi⟩ := (hev.and hIoi).exists
    have ht1 : 1 < t := htIoi
    obtain ⟨w, hwε, hwF⟩ := hδ _ (by rwa [Metric.mem_ball, dist_eq_norm] at htball)
    have hwball : w ∈ Metric.ball z ε := by rwa [Metric.mem_ball, dist_eq_norm]
    have hwU : w ∈ Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)) :=
      hεU hwball
    have hwray : Work.EL.F c w ∈ Work.EL.paramRay d.hN P.a := by
      rw [hwF]; exact Work.EL.rayPt_mem_paramRay d.hN ht1
    exact pullQ_notMem_paramRay I hadm n hP hwU hwray
  -- ## conclusion
  have hcompl : Work.EL.F c '' Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))
      ⊆ (Work.EL.polyCurve [P0, N.Qp n] (Work.ELNest.Qlev L n))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Set.mem_compl_iff]
    by_cases hzK : z ∈ Work.EL.K c
    · exact hKpart z hz hzK
    · exact Work.EL.polyRegion_subset_compl [P0, N.Qp n] (Work.ELNest.Qlev L n)
        (hnonK z hz hzK)
  set seed : ℂ := Work.EL.rayPt d.hN
    (Work.EL.midNear [P0, N.Qp (n + 1)]) (Real.sqrt (Work.ELNest.Qlev L (n + 1))) with hseed
  have hseedU : seed ∈ Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)) :=
    Work.ELTop.seed_mem_polyRegion d.hN _ hAdm' hR'
  have hseedK : seed ∉ Work.EL.K c := Work.EL.rayPt_notMem_K d.hN (one_lt_sqrt hR')
  have hseedV : Work.EL.F c seed ∈ Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n) :=
    hnonK seed hseedU hseedK
  have hpre : IsPreconnected (Work.EL.F c ''
      Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))) :=
    (Work.EL.isPreconnected_polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))).image _
      (continuous_F c).continuousOn
  have hsub : Work.EL.F c '' Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))
      ⊆ Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n) := by
    have h := hpre.subset_connectedComponentIn ⟨seed, hseedU, rfl⟩ hcompl
    have heq : connectedComponentIn (Work.EL.polyCurve [P0, N.Qp n] (Work.ELNest.Qlev L n))ᶜ
        (Work.EL.rayPt d.hN (Work.EL.midNear [P0, N.Qp n]) (Real.sqrt (Work.ELNest.Qlev L n)))
        = connectedComponentIn (Work.EL.polyCurve [P0, N.Qp n] (Work.ELNest.Qlev L n))ᶜ
          (Work.EL.F c seed) := connectedComponentIn_eq hseedV
    have hpoly : Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n)
        = connectedComponentIn (Work.EL.polyCurve [P0, N.Qp n] (Work.ELNest.Qlev L n))ᶜ
          (Work.EL.rayPt d.hN (Work.EL.midNear [P0, N.Qp n])
            (Real.sqrt (Work.ELNest.Qlev L n))) := rfl
    rw [hpoly, heq]
    exact h
  intro z hz
  exact hsub ⟨z, hz, rfl⟩

/-- `F c` is a covering map over the level-`n` region. -/
theorem pullQ_cov {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N) (n : ℕ) :
    IsCoveringMapOn (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n)) := by
  refine Work.ELPull.isCoveringMapOn_tsqIterate_mono c 5 ?_
  intro w hw
  rw [Set.mem_compl_iff]
  rintro ⟨z, hz, hzw⟩
  obtain ⟨k, hk, hkz⟩ := Work.ELPull.critValues_tsqIterate (c := c) 5 z hz
  exact I.hcv n k (by simpa [Finset.mem_Icc, Set.mem_Icc] using hk)
    (by rw [← hkz, hzw]; exact hw)


/-! ## The boundary correspondence -/

/-- The parameter ray depends on the angle only modulo `1`: `paramRay θ = paramRay θ'` forces
`θ' ≡ θ`. -/
theorem paramRay_eq_angle {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ θ' : ℝ}
    (h : Work.EL.paramRay hN θ = Work.EL.paramRay hN θ') : ∃ k : ℤ, θ' = θ + k := by
  have h2 : Work.EL.rayPt hN θ 2 ∈ Work.EL.paramRay hN θ' := by
    rw [← h]; exact Work.EL.rayPt_mem_paramRay hN (by norm_num)
  rw [Work.Top.NakaneData.mem_paramRay_iff] at h2
  obtain ⟨-, t, ht, hΦ⟩ := h2
  rw [Work.Top.NakaneData.Phi_rayPt hN (by norm_num : (1:ℝ) < 2)] at hΦ
  have ht_eq : t = 2 := by
    have h1 := congrArg norm hΦ
    rw [Work.Top.NakaneData.norm_rayPoint, Work.Top.NakaneData.norm_rayPoint] at h1
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos (by linarith : (0:ℝ) < t)] at h1
    linarith
  subst ht_eq
  exact Work.ELTop.rayPoint_angle_eq_int (by norm_num : (1:ℝ) < 2) hΦ

/-- Landing is insensitive to shifting the angle by an integer. -/
theorem landsN_of_angle_eq {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} (θ θ' : ℝ)
    (h : ∃ k : ℤ, θ' = θ + k) {y : ℂ} (hθ : Work.EL.LandsN hN θ' y) : Work.EL.LandsN hN θ y := by
  obtain ⟨k, rfl⟩ := h
  have hfun : (fun t : ℝ => Work.EL.rayPt hN (θ + (k:ℝ)) t)
      = fun t : ℝ => Work.EL.rayPt hN θ t := by
    funext t; exact Work.ELTop.rayPt_add_int hN θ t k
  show Filter.Tendsto (fun t : ℝ => Work.EL.rayPt hN θ t)
    (nhdsWithin (1:ℝ) (Set.Ioi 1)) (𝓝 y)
  rw [← hfun]
  exact hθ

/-- The vertex of a ray polygon lies on it. -/
theorem mem_polyCurve_vertex {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {ps : List (Work.EL.CoPair hN)} {R : ℝ} {P : Work.EL.CoPair hN} (hP : P ∈ ps) :
    P.y ∈ Work.EL.polyCurve ps R := by
  rw [Work.EL.polyCurve]; simp only [Set.mem_ofPred_eq]
  exact Or.inl ⟨P, hP, Or.inl rfl⟩

/-- The ray piece at the first angle of a pair of the polygon lies on it. -/
theorem mem_polyCurve_rayPiece_a {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {ps : List (Work.EL.CoPair hN)} {R : ℝ} {P : Work.EL.CoPair hN} (hP : P ∈ ps) {z : ℂ}
    (hz : z ∈ Work.EL.rayPiece hN P.a 0 R) : z ∈ Work.EL.polyCurve ps R := by
  rw [Work.EL.polyCurve]; simp only [Set.mem_ofPred_eq]
  exact Or.inl ⟨P, hP, Or.inr (Or.inl hz)⟩

/-- The ray piece at the second angle of a pair of the polygon lies on it. -/
theorem mem_polyCurve_rayPiece_b {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {ps : List (Work.EL.CoPair hN)} {R : ℝ} {P : Work.EL.CoPair hN} (hP : P ∈ ps) {z : ℂ}
    (hz : z ∈ Work.EL.rayPiece hN P.b 0 R) : z ∈ Work.EL.polyCurve ps R := by
  rw [Work.EL.polyCurve]; simp only [Set.mem_ofPred_eq]
  exact Or.inl ⟨P, hP, Or.inr (Or.inr hz)⟩

/-- `rayPt hN β s` (with `1 < s ≤ R` and `β` one of the two angles of a pair `P ∈ ps`) lies on
the polygon. -/
theorem rayPt_mem_polyCurve_rayPiece {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {ps : List (Work.EL.CoPair hN)} {R : ℝ} {P : Work.EL.CoPair hN} (hP : P ∈ ps) {ab : ℝ}
    (hab : ab = P.a ∨ ab = P.b) {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ R) :
    Work.EL.rayPt hN ab s ∈ Work.EL.polyCurve ps R := by
  have hmem : Work.EL.rayPt hN ab s ∈ Work.EL.rayPiece hN ab 0 R := by
    refine ⟨Work.EL.rayPt_mem_paramRay hN hs1, Work.EL.pot_nonneg hN _, ?_⟩
    have h1 : Work.EL.pot hN (Work.EL.rayPt hN ab s) = Real.log s := Work.EL.pot_rayPt hN hs1
    have h2 : Real.log s ≤ Real.log R := Real.log_le_log (by linarith) hs2
    exact h1.trans_le h2
  rcases hab with rfl | rfl
  · exact mem_polyCurve_rayPiece_a hP hmem
  · exact mem_polyCurve_rayPiece_b hP hmem

/-- A point of a ray piece is a ray point of a level in `(1, R]`. -/
theorem eq_rayPt_of_mem_rayPiece {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    {β t₀ R : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ Work.EL.rayPiece hN β t₀ R) :
    ∃ t : ℝ, 1 < t ∧ t ≤ R ∧ z = Work.EL.rayPt hN β t := by
  have hp : z ∈ Work.EL.paramRay hN β := hz.1
  rw [Work.Top.NakaneData.mem_paramRay_iff] at hp
  obtain ⟨hzK, t, ht, hΦ⟩ := hp
  refine ⟨t, ht, ?_, ?_⟩
  · have hpot : Work.EL.pot hN z = Real.log t := by
      rw [Work.EL.pot_of_notMem hN hzK, hΦ, Work.Top.NakaneData.norm_rayPoint,
        abs_of_pos (by linarith : (0:ℝ) < t)]
    have h2 : Real.log t ≤ Real.log R := by rw [← hpot]; exact hz.2.2
    exact (Real.log_le_log_iff (by linarith) hR).mp h2
  · have h2 : Work.EL.rayPt hN β t = z :=
      hN.injOn_Phi (hN.rayPt_notMem ht) hzK
        ((Work.Top.NakaneData.Phi_rayPt hN ht).trans hΦ.symm)
    exact h2.symm

/-- **The first angles of the level-`(n+1)` polygon map to angles of the level-`n` polygon.** -/
theorem pullQ_a_image {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N) (n : ℕ) :
    ∀ P' ∈ [P0, N.Qp (n + 1)], ∃ P ∈ [P0, N.Qp n], ∃ k : ℤ,
      Work.EL.T^[10] P'.a = P.a + k ∨ Work.EL.T^[10] P'.a = P.b + k := by
  intro P' hP'
  obtain ⟨P, hP, h⟩ := I.pair n P' hP'
  refine ⟨P, hP, ?_⟩
  rcases h with h | h
  · obtain ⟨k, hk⟩ := paramRay_eq_angle d.hN h.symm
    exact ⟨k, Or.inl hk⟩
  · obtain ⟨k, hk⟩ := paramRay_eq_angle d.hN h.symm
    exact ⟨k, Or.inr hk⟩

/-- **The second angles of the level-`(n+1)` polygon map to angles of the level-`n` polygon**
(the `βₙ'`-`βₙ+1` arithmetic of the `z₁`-nest; this is why `P0` has to be the `α`-pair). -/
theorem pullQ_b_image {c : ℂ} {d : Work.EL.RootParabolic c} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (hP0 : P0.a = Work.EL.alpha1 ∧ P0.b = Work.EL.alpha2) (n : ℕ) :
    ∀ P' ∈ [P0, N.Qp (n + 1)], ∃ P ∈ [P0, N.Qp n], ∃ k : ℤ,
      Work.EL.T^[10] P'.b = P.b + k := by
  intro P' hP'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
  rcases hP' with h | h
  · rw [h]
    refine ⟨P0, by simp, 0, ?_⟩
    rw [hP0.2, Work.ELAssembly.T_ten_alpha2]; ring
  · rw [h]
    refine ⟨N.Qp n, by simp, -1, ?_⟩
    rw [N.Qpb (n+1), N.Qpb n, Work.ELAssembly.T_ten_add_one, (Work.ELNest.T_iterate_bAng n).1]
    ring

/-- **The boundary of the level-`(n+1)` polygon maps into the boundary of the level-`n`
polygon.** -/
theorem pullQ_boundary_map {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) (n : ℕ)
    (hP0 : P0.a = Work.EL.alpha1 ∧ P0.b = Work.EL.alpha2) :
    Work.EL.F c '' Work.EL.polyCurve [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))
      ⊆ Work.EL.polyCurve [P0, N.Qp n] (Work.ELNest.Qlev L n) := by
  have hL := I.hL
  have hR' : 1 < Work.ELNest.Qlev L (n + 1) := (Work.ELNest.Qlev_facts hL (n + 1)).1
  have hR : 1 < Work.ELNest.Qlev L n := (Work.ELNest.Qlev_facts hL n).1
  have hpow := Qlev_succ_pow hL n
  -- the ray-point identity: `F c (rayPt β s) = rayPt (T^[10] β) (s^1024)`
  have hFray : ∀ β s : ℝ, 1 < s →
      Work.EL.F c (Work.EL.rayPt d.hN β s)
        = Work.EL.rayPt d.hN (Work.EL.T^[10] β) (s ^ 1024) := by
    intro β s hs
    rw [Work.ELAssembly.EL_F_eq_tantibar]
    have h := Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher (θ := β) (t := s) hs 10
    simpa using h
  rintro _ ⟨z, hz, rfl⟩
  rw [Work.EL.polyCurve] at hz
  simp only [Set.mem_ofPred_eq] at hz
  rcases hz with ⟨P', hP', hzy | hza | hzb⟩ | ⟨θ, hθ, hfar, hzθ⟩
  · -- a vertex of the level-`(n+1)` polygon
    subst hzy
    obtain ⟨P, hP, k, hk | hk⟩ := pullQ_a_image I n P' hP'
    · have hlands : Work.EL.LandsN d.hN (Work.EL.T^[10] P'.a) (Work.EL.F c P'.y) :=
        Work.ELNest.landsN_iterate_F d.hN d.bottcher P'.lands_a
      have hlands' : Work.EL.LandsN d.hN (Work.EL.T^[10] P'.a) P.y :=
        landsN_of_angle_eq (Work.EL.T^[10] P'.a) P.a ⟨-k, by rw [hk]; push_cast; ring⟩ P.lands_a
      have heq : Work.EL.F c P'.y = P.y := Work.ELNest.landsN_unique hlands hlands'
      rw [heq]; exact mem_polyCurve_vertex hP
    · have hlands : Work.EL.LandsN d.hN (Work.EL.T^[10] P'.a) (Work.EL.F c P'.y) :=
        Work.ELNest.landsN_iterate_F d.hN d.bottcher P'.lands_a
      have hlands' : Work.EL.LandsN d.hN (Work.EL.T^[10] P'.a) P.y :=
        landsN_of_angle_eq (Work.EL.T^[10] P'.a) P.b ⟨-k, by rw [hk]; push_cast; ring⟩ P.lands_b
      have heq : Work.EL.F c P'.y = P.y := Work.ELNest.landsN_unique hlands hlands'
      rw [heq]; exact mem_polyCurve_vertex hP
  · -- the ray piece at `P'.a`
    obtain ⟨t, ht1, htR, rfl⟩ := eq_rayPt_of_mem_rayPiece (by linarith : (0:ℝ) < Work.ELNest.Qlev L (n + 1)) hza
    obtain ⟨P, hP, k, hk | hk⟩ := pullQ_a_image I n P' hP'
    · rw [hFray P'.a t ht1, hk, Work.ELTop.rayPt_add_int]
      refine rayPt_mem_polyCurve_rayPiece hP (Or.inl rfl) (one_lt_pow₀ ht1 (by norm_num)) ?_
      calc t ^ 1024 ≤ (Work.ELNest.Qlev L (n + 1)) ^ 1024 :=
            pow_le_pow_left₀ (by linarith) htR 1024
        _ = Work.ELNest.Qlev L n := hpow
    · rw [hFray P'.a t ht1, hk, Work.ELTop.rayPt_add_int]
      refine rayPt_mem_polyCurve_rayPiece hP (Or.inr rfl) (one_lt_pow₀ ht1 (by norm_num)) ?_
      calc t ^ 1024 ≤ (Work.ELNest.Qlev L (n + 1)) ^ 1024 :=
            pow_le_pow_left₀ (by linarith) htR 1024
        _ = Work.ELNest.Qlev L n := hpow
  · -- the ray piece at `P'.b`
    obtain ⟨t, ht1, htR, rfl⟩ := eq_rayPt_of_mem_rayPiece (by linarith : (0:ℝ) < Work.ELNest.Qlev L (n + 1)) hzb
    obtain ⟨P, hP, k, hk⟩ := pullQ_b_image hP0 n P' hP'
    rw [hFray P'.b t ht1, hk, Work.ELTop.rayPt_add_int]
    refine rayPt_mem_polyCurve_rayPiece hP (Or.inr rfl) (one_lt_pow₀ ht1 (by norm_num)) ?_
    calc t ^ 1024 ≤ (Work.ELNest.Qlev L (n + 1)) ^ 1024 :=
          pow_le_pow_left₀ (by linarith) htR 1024
      _ = Work.ELNest.Qlev L n := hpow
  · -- the equipotential arc
    subst hzθ
    by_cases hcl : ∃ P' ∈ [P0, N.Qp (n + 1)], Work.EL.InClosedArc θ P'.a P'.b
    · obtain ⟨P', hP', hcl'⟩ := hcl
      have hfr : Int.fract (θ - P'.a) = 0 ∨ Int.fract (θ - P'.a) = Work.EL.arcLen P'.a P'.b := by
        rcases lt_or_eq_of_le hcl'.1 with hpos | hzero
        · rcases lt_or_eq_of_le hcl'.2 with hlt | heq
          · exact absurd ⟨hpos, hlt⟩ (hfar P' hP')
          · exact Or.inr heq
        · exact Or.inl hzero.symm
      rcases hfr with h0 | hlen
      · obtain ⟨j, hj⟩ := Int.fract_eq_zero_iff.mp h0
        have hθeq : θ = P'.a + (j : ℝ) := by linarith
        have hzeq : Work.EL.rayPt d.hN θ (Work.ELNest.Qlev L (n + 1))
            = Work.EL.rayPt d.hN P'.a (Work.ELNest.Qlev L (n + 1)) := by
          rw [hθeq]; exact Work.ELTop.rayPt_add_int d.hN P'.a _ j
        obtain ⟨P, hP, k, hk | hk⟩ := pullQ_a_image I n P' hP'
        · rw [hzeq, hFray P'.a _ hR', hk, Work.ELTop.rayPt_add_int]
          refine rayPt_mem_polyCurve_rayPiece hP (Or.inl rfl) (one_lt_pow₀ hR' (by norm_num)) ?_
          rw [hpow]
        · rw [hzeq, hFray P'.a _ hR', hk, Work.ELTop.rayPt_add_int]
          refine rayPt_mem_polyCurve_rayPiece hP (Or.inr rfl) (one_lt_pow₀ hR' (by norm_num)) ?_
          rw [hpow]
      · rw [Work.EL.arcLen] at hlen
        obtain ⟨j, hj⟩ := Int.fract_eq_fract.mp hlen
        have hθeq : θ = P'.b + (j : ℝ) := by linarith
        have hzeq : Work.EL.rayPt d.hN θ (Work.ELNest.Qlev L (n + 1))
            = Work.EL.rayPt d.hN P'.b (Work.ELNest.Qlev L (n + 1)) := by
          rw [hθeq]; exact Work.ELTop.rayPt_add_int d.hN P'.b _ j
        obtain ⟨P, hP, k, hk⟩ := pullQ_b_image hP0 n P' hP'
        rw [hzeq, hFray P'.b _ hR', hk, Work.ELTop.rayPt_add_int]
        refine rayPt_mem_polyCurve_rayPiece hP (Or.inr rfl) (one_lt_pow₀ hR' (by norm_num)) ?_
        rw [hpow]
    · push_neg at hcl
      rw [hFray θ _ hR', hpow]
      refine Work.ELTop.rayPt_mem_polyCurve_of_notInArc d.hN [P0, N.Qp n] hR ?_
      intro P hP hin
      exact (I.arc n θ hcl P hP) (Work.EL.InArc.inClosedArc hin)

/-- **The level-`(n+1)` region is closed under `F c` in the level-`n` region** (the `hcl`
hypothesis of the covering criterion). -/
theorem pullQ_cl {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) (n : ℕ) :
    ∀ x ∈ closure (Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))),
      Work.EL.F c x ∈ Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n) →
      x ∈ Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)) := by
  have hL := I.hL
  have hR' : 1 < Work.ELNest.Qlev L (n + 1) := (Work.ELNest.Qlev_facts hL (n + 1)).1
  have hJ := Work.TopJordan.jordanForm
  have hP0 := pullQ_P0_eq I hadm
  have hbmap := pullQ_boundary_map I hadm n hP0
  have hfront : frontier (Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)))
      = Work.EL.polyCurve [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)) :=
    Work.ELTop.frontier_polyRegion_eq_polyCurve d.hN hJ _ (hadm (n + 1)) hR'
      (Work.ELTop.polyCurve_isJordan d.hN _ (hadm (n + 1)) hR')
  intro x hx hFxV
  rw [closure_eq_self_union_frontier, hfront] at hx
  rcases hx with hxU | hxC
  · exact hxU
  · exact absurd (hbmap ⟨x, hxC, rfl⟩)
      (fun h => (Work.EL.polyRegion_subset_compl [P0, N.Qp n] (Work.ELNest.Qlev L n) hFxV) h)

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **The pull-back `pbQ` of the `z₁`-nest**: `F c = (Tantibar c)^[10]` maps the level-`(n+1)`
region `[P₀, Qp(n+1)]` bijectively onto the level-`n` region `[P₀, Qp n]`.  The proof is the
covering-plus-one-fibre criterion `Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre` applied to
`U = polyRegion [P0, N.Qp (n+1)] (Qlev L (n+1))`, `V = polyRegion [P0, N.Qp n] (Qlev L n)`:
the covering comes from `Work.ELPull.isCoveringMapOn_tsqIterate_mono` (`m = 5`) with
`Work.ELPull.critValues_tsqIterate` and `I.hcv` (`(Tantibar c)^[k] 0 ∉ V` for `k = 1..10`),
`V ⊇ F '' U` from `mem_polyRegion_iff_of_notMem_K` (`I.arc` for `U ∖ K`, the landing-point
argument for `U ∩ K`), the closedness `hcl` from `frontier_polyRegion_eq_polyCurve` (`I.pair`),
and the fibre condition at `v₀ = rayPt (midNear [P0, N.Qp n]) (Real.sqrt (Qlev L n))`
(`seed_mem_polyRegion`) from `I.one`.  The admissibility hypotheses come from
`Work.ELAssembly.Q_adm_of`; `polyCurve_isJordan` from ELTop supplies the Jordan-curve inputs;
openness of `U`, `V` is `Work.ELTop.isOpen_polyRegion`; `Work.TopJordan.jordanForm` supplies the
`JordanForm` argument of the ELTop lemmas. -/
theorem pullQ_bij {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {P0 : Work.EL.CoPair d.hN}
    {N : NestPairs d} (I : QPullInputs c d L P0 N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [P0, N.Qp n]) (n : ℕ) :
    Set.BijOn (Work.EL.F c)
      (Work.EL.polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)))
      (Work.EL.polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n)) := by
  have hL := I.hL
  have hR' : 1 < Work.ELNest.Qlev L (n + 1) := (Work.ELNest.Qlev_facts hL (n + 1)).1
  have hR : 1 < Work.ELNest.Qlev L n := (Work.ELNest.Qlev_facts hL n).1
  exact Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre (f := Work.EL.F c)
    (continuous_F c) (pullQ_cov I n)
    (Work.ELTop.isOpen_polyRegion d.hN [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))
      (Work.ELTop.isClosed_polyCurve d.hN [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1))))
    (Work.EL.isPreconnected_polyRegion [P0, N.Qp (n + 1)] (Work.ELNest.Qlev L (n + 1)))
    (Work.ELTop.polyRegion_nonempty d.hN [P0, N.Qp (n + 1)] (hadm (n + 1)) hR')
    (Work.ELTop.isOpen_polyRegion d.hN [P0, N.Qp n] (Work.ELNest.Qlev L n)
      (Work.ELTop.isClosed_polyCurve d.hN [P0, N.Qp n] (Work.ELNest.Qlev L n)))
    (Work.EL.isPreconnected_polyRegion [P0, N.Qp n] (Work.ELNest.Qlev L n))
    (pullQ_map I hadm n) (pullQ_cl I hadm n)
    (Work.ELTop.seed_mem_polyRegion d.hN [P0, N.Qp n] (hadm n) hR)
    (pullQ_fib I hadm n)

end Work.ELAssembly
