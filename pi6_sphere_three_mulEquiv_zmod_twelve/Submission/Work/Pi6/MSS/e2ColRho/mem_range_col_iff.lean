import Mathlib
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSS.e2ColRho.mssCol_mkQ
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

namespace Work.Pi6.MSS.e2ColRho

open Work.Pi6.MSS

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (e₀ : E)

/-! ## Degree bookkeeping for the fibre edge of the zeroth column.

The bidegree `(0,q)` has `ℕ`-indices `EI ((0:ℤ),(q:ℤ)) = 0` and
`EN ((0:ℤ),(q:ℤ)) = 0 + q`, so every statement about the column carries a transport
`0 + q = q`.  We record the small module-theoretic facts used to move such transports past
pullback along the fibre inclusion and past the class of a transported cocycle. -/

/-- The degree cast of `cmap` along an equality of degrees. -/
theorem cmap_cohXcast_apply {m k : ℕ} (h : m = k) (y : Work.Pi6.Coh 𝕜 E m) :
    cohXcast 𝕜 E B p e₀ h ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) m).hom y)
      = (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) k).hom (h ▸ y) := by
  cases h
  rw [cohXcast_rfl]
  rfl

/-- `CohFilt.xcast` is the `Eq.rec` transport. -/
theorem cochain_xcast_eq_eqRec {a b : ℕ} (h : a = b) (x : (serreCF 𝕜 E B p).C.X a) :
    (serreCF 𝕜 E B p).xcast h x = h ▸ x := by
  subst h
  rw [CohFilt.xcast_rfl]
  rfl

/-- Round trip of a degree transport. -/
theorem eqRec_coh_symm_self {m k : ℕ} (h : k = m) (y : Work.Pi6.Coh 𝕜 E m) :
    h ▸ (h.symm ▸ y) = y := by cases h; rfl

/-- The degree cast of the class of a transported cocycle. -/
theorem eqRec_classOf_xcast_coh {m k : ℕ} (h : k = m)
    (β : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m)
    (hβ : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) β = 0)
    (hβ' : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E)
      ((serreCF 𝕜 E B p).xcast h.symm β) = 0) :
    h ▸ (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E)
        ((serreCF 𝕜 E B p).xcast h.symm β) hβ')
      = Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) β hβ := by
  have h1 : (serreCF 𝕜 E B p).xcast h.symm β = h.symm ▸ β :=
    cochain_xcast_eq_eqRec 𝕜 E B p h.symm β
  have hclass : Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E)
        ((serreCF 𝕜 E B p).xcast h.symm β) hβ'
      = Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) (h.symm ▸ β)
          (Work.Cohomology.cochainDiff_cast 𝕜 (Work.SSS.sSing E) h.symm β hβ) :=
    Work.Cohomology.cohomologyClassOf_congr 𝕜 (Work.SSS.sSing E) h1 hβ' _
  rw [hclass]
  rw [← Work.Cohomology.cohomologyClassOf_cast 𝕜 (Work.SSS.sSing E) h.symm β hβ]
  exact eqRec_coh_symm_self 𝕜 E h
    (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) β hβ)

/-- `Work.Pi6.MSS.mssColIter_mkQ` with the bidegree `(0,q)` written out as the `ℕ`-indices
`0` and `0 + q`. -/
theorem mssColIter_mkQ_zeroAdd (q k : ℕ)
    (w : ↥(pZ 𝕜 (serreCF 𝕜 E B p) (k+2) 0 (0+q))) :
    mssColIter 𝕜 E B p q k
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (k+2) 0 (0+q)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) (k+2) 0 (0+q)).subtype) w)
      = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 (0+q)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 (0+q)).subtype)
          ⟨w.1, pd_pZ_anti (by omega) le_rfl w.2⟩ :=
  mssColIter_mkQ 𝕜 E B p q k w

/-! ## The two halves of the fibre edge -/

/-- **A cocycle of `E` dies of the column `E_{q+2}^{0,q}`.**  The class of the cocycle `α`
(transported to the degree `0 + q` of the bidegree `(0,q)`) lies in the image of the iterated
column inclusion, and the restriction-to-the-fibre isomorphism sends it to the pullback of `α`
along the fibre inclusion.  This is the `(⇒)` half of the fibre edge. -/
theorem exists_col_of_cocycle (N q : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) (hq : q ≤ N)
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (hα : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) α = 0) :
    ∃ z : Work.Pi6.MSS.mssE 𝕜 (serreCF 𝕜 E B p) (q+2) ((0:ℤ),(q:ℤ)),
      Work.Pi6.MSS.mssColIter 𝕜 E B p q q z =
        (Work.Pi6.MSS.rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm
          ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom
            (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) α hα)) := by
  change ∃ z : pEraw 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q),
      Work.Pi6.MSS.mssColIter 𝕜 E B p q q z =
        (Work.Pi6.MSS.rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm
          ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom
            (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) α hα))
  have h1' : q + 1 = (0+q)+1 := congrArg (fun n => n + 1) ((Nat.zero_add q).symm)
  let β : (serreCF 𝕜 E B p).C.X (0+q) :=
    (serreCF 𝕜 E B p).xcast ((Nat.zero_add q).symm) α
  have hβ : (serreCF 𝕜 E B p).d (0+q) β = 0 := by
    have key := pd_xcast_d (𝕜 := 𝕜) (W := serreCF 𝕜 E B p)
      (a := q) (b := 0+q) ((Nat.zero_add q).symm) h1' α
    have key2 : ((serreCF 𝕜 E B p).xcast h1') (((serreCF 𝕜 E B p).d q) α) = 0 := by
      rw [serreCF_d_apply 𝕜 E B p q α, hα, map_zero]
    exact key.symm.trans key2
  have hd : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) β = 0 :=
    (serreCF_d_apply 𝕜 E B p (0+q) β).symm.trans hβ
  have hmem : β ∈ pZ 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q) := by
    refine ⟨?_, ?_⟩
    · show β ∈ (serreCF 𝕜 E B p).F 0 (0+q)
      rw [(serreCF 𝕜 E B p).F_zero]; exact Submodule.mem_top
    · show (serreCF 𝕜 E B p).d (0+q) β ∈ (serreCF 𝕜 E B p).F (0+(q+2)) (0+q+1)
      rw [hβ]; exact Submodule.zero_mem _
  have hmem2 : β ∈ pZ 𝕜 (serreCF 𝕜 E B p) 2 0 (0+q) := by
    refine ⟨?_, ?_⟩
    · show β ∈ (serreCF 𝕜 E B p).F 0 (0+q)
      rw [(serreCF 𝕜 E B p).F_zero]; exact Submodule.mem_top
    · show (serreCF 𝕜 E B p).d (0+q) β ∈ (serreCF 𝕜 E B p).F (0+2) (0+q+1)
      rw [hβ]; exact Submodule.zero_mem _
  refine ⟨Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q)).comap
      (pZ 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q)).subtype) ⟨β, hmem⟩, ?_⟩
  rw [LinearEquiv.eq_symm_apply]
  rw [rhoSSEquiv_apply]
  rw [mssColIter_mkQ_zeroAdd]
  rw [rho_mkQ_cocycle]
  rw [cmap_cohXcast_apply]
  congr 1
  exact eqRec_classOf_xcast_coh 𝕜 E B p (Nat.zero_add q) α hα hd

/-- **The fibre edge.**  If the class of an element of `E_{q+2}^{0,q}` maps to `f` under the
restriction-to-the-fibre isomorphism, then `f` is the restriction of a class of `E`.  This is the
`(⇐)` half of the fibre edge. -/
theorem exists_cmap_eq_of_col (N q : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) (hq : q ≤ N)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (z : Work.Pi6.MSS.mssE 𝕜 (serreCF 𝕜 E B p) (q+2) ((0:ℤ),(q:ℤ)))
    (hz : Work.Pi6.MSS.mssColIter 𝕜 E B p q q z =
      (Work.Pi6.MSS.rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm f) :
    ∃ e : Work.Pi6.Coh 𝕜 E q,
      (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f := by
  let z' : pEraw 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q) := z
  have hz' : Work.Pi6.MSS.mssColIter 𝕜 E B p q q z' =
      (Work.Pi6.MSS.rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm f := hz
  have hf : Work.Pi6.MSS.rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq
      (Work.Pi6.MSS.mssColIter 𝕜 E B p q q z') = f :=
    (LinearEquiv.eq_symm_apply _).mp hz'
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q)).comap
      (pZ 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q)).subtype) z'
  have hder : (serreCF 𝕜 E B p).d (0+q) w.1 = 0 := by
    have hmemF : (serreCF 𝕜 E B p).d (0+q) w.1 ∈
        (serreCF 𝕜 E B p).F (0+(q+2)) ((0+q)+1) := w.2.2
    have hbot : (serreCF 𝕜 E B p).F (0+(q+2)) ((0+q)+1) = ⊥ := by
      rw [show (0+(q+2) : ℕ) = ((0+q)+1)+1 from rfl, (serreCF 𝕜 E B p).F_top ((0+q)+1)]
    rw [hbot, Submodule.mem_bot] at hmemF
    exact hmemF
  have hd : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) w.1 = 0 :=
    (serreCF_d_apply 𝕜 E B p (0+q) w.1).symm.trans hder
  have hstep : Work.Pi6.MSS.rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq
      (Work.Pi6.MSS.mssColIter 𝕜 E B p q q
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) (q+2) 0 (0+q)).subtype) w))
      = (cohXcast 𝕜 E B p e₀ (Nat.zero_add q))
          ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) (0+q)).hom
            (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) w.1 hd)) := by
    rw [mssColIter_mkQ_zeroAdd, rhoSSEquiv_apply, rho_mkQ_cocycle]
  have hX : (cohXcast 𝕜 E B p e₀ (Nat.zero_add q))
      ((Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) (0+q)).hom
        (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) w.1 hd)) = f := by
    rw [← hstep, hw]
    exact hf
  exact ⟨(Nat.zero_add q) ▸
      (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) w.1 hd),
    (cmap_cohXcast_apply (𝕜 := 𝕜) (E := E) (B := B) (p := p) (e₀ := e₀)
      (h := Nat.zero_add q)
      (y := Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) w.1 hd)).symm.trans hX⟩

/-- **The fibre edge of the zeroth column.** A class `f ∈ H^q(F)` is the restriction of a class of
`E` exactly when its image under the inverse of `rhoSSEquiv` lies in the image of the iterated column
inclusion `E_{q+2}^{0,q} → E_2^{0,q}`.  This is clause 3 of `Work.Pi6.MSS.e2Col_exists` for
`col = rhoSSEquiv.symm`.  Do NOT import `Submission/Work/Pi6/MSS/e2ColRho/rhoSS_mssColIter.lean`; do
the computation inline (ingredients: `Work.Pi6.MSS.mssColIter_mkQ` (proved in `e2ColRho`),
`Work.Pi6.MSS.rhoSSEquiv_apply`, `Work.Pi6.MSS.rho_mkQ`, `Work.Pi6.MSS.rho_mkQ_cocycle`,
`Work.Pi6.MSS.resCochain_xcast`, `cohXcast_comp_apply`, `cohXcast_congr`,
`Work.Cohomology.exists_cohomologyClassOf`, `Work.Pi6.MSS.mem_pZ_of_cocycle`,
`Work.Pi6.MSS.pd_pZ_xcast`, `pd_xcast_d`, `pd_transport_mem`, `(serreCF 𝕜 E B p).F_top (q+1)`,
`Subsingleton.elim` for the degree equalities).

For `(⇒)`: take a cocycle `α` of `E` in degree `q` representing `e`, transport it to the `ℕ`-indices
of the bidegree `(0,q)` by `(serreCF 𝕜 E B p).xcast
((Nat.zero_add q).symm.trans (EN_pair 0 q).symm)` and `pd_pZ_xcast (rfl : 0 = EI ((0:ℤ),(q:ℤ))) _`
(`α ∈ pZ (q+2) 0 q` by `mem_pZ_of_cocycle`), and use `mssColIter_mkQ` + `rhoSSEquiv_apply` +
`rho_mkQ_cocycle`.

For `(⇐)`: given `z = mkQ w`, apply `rhoSSEquiv` to the hypothesis and identify the result with
`(cmap fibreIncl q) e` for `e := [xcast h w.1]` with `h : q = EN ((0:ℤ),(q:ℤ))`; the cocycle
condition for that element follows from `pd_xcast_d`/`pd_transport_mem` and
`(serreCF 𝕜 E B p).F_top (q+1)` (note `q + 2 ≥ 0 + q + 2`, so `F^{q+2}(0+q+1) = ⊥`). -/
theorem mem_range_col_iff (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N q : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) (hq : q ≤ N)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (∃ e : Work.Pi6.Coh 𝕜 E q,
        (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f) ↔
      ∃ z : Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) (q + 2) ((0 : ℤ), (q : ℤ)),
        Work.Pi6.MSS.mssColIter 𝕜 E B p q q z =
          (Work.Pi6.MSS.rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm f := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf 𝕜 (Work.SSS.sSing E) q e
    rw [← he]
    exact exists_col_of_cocycle 𝕜 E B p e₀ N q hfib hconn hfin hq α hα
  · rintro ⟨z, hz⟩
    exact exists_cmap_eq_of_col 𝕜 E B p e₀ N q hfib hconn hfin hq f z hz

end

end Work.Pi6.MSS.e2ColRho
