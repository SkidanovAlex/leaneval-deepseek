import Mathlib
import Submission.Work.Pi6.MSS.e2ColAux
import Submission.Work.Pi6.MSS.e2Col_coFilt_ker_res
import Submission.Work.Pi6.MSS.e2Col_fibre_kernel
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.mssMulCompat
import Submission.Work.Pi6.MSS.mulEq
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupH
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Pi6.MSS.e2ColRho.classZero_vanishes
import Submission.Work.Pi6.MSS.e2ColRho.finrank_col
import Submission.Work.Pi6.MSS.e2ColRho.mssCol_mkQ
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-!
# The restriction-to-the-fibre map on the column of `E_2`

For a Serre fibration `p : E → B` over a simply connected base, the zeroth column of the second page
of the Serre spectral sequence is the cohomology of the fibre `F = p⁻¹(p e₀)`.  This file builds
the comparison map

`rho : E_2^{0,q} ⟶ H^q(F)`

by restricting a `2`-cycle of the Serre cochain filtration to the fibre (well defined because the
denominator `Z_1^1 + B_2^0` consists of cochains vanishing on the fibre and of coboundaries), and
proves its basic properties: its value on the class of a cycle, the vanishing of the denominator
(so that it descends to `E_2^{0,q}`) and its compatibility with the cup products.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (e₀ : E)

/-! ## 1. The differentials of the Serre filtration -/

theorem serreCF_d_apply (q : ℕ) (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q) :
    (serreCF 𝕜 E B p).d q x = Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x := by
  rw [CohFilt.d]
  show ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).d q (q + 1)).hom x = _
  rw [Work.Cohomology.SSetCochainComplex_d]
  rfl

/-! ## 2. The restriction map on the `2`-cycles -/

/-- The restriction of a `2`-cycle of the column to the fibre is a cocycle. -/
theorem resCochain_cyc (q : ℕ) (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q)) :
    Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
      (resCochain 𝕜 E B p e₀ q x.1) = 0 := by
  rw [(resCochain_d 𝕜 E B p e₀ q x.1).symm]
  refine e2Col_coFilt_ker_res 𝕜 E B p e₀ (q + 1) _ ((serreCF 𝕜 E B p).F_mono 1 (q + 1) ?_)
  rw [← serreCF_d_apply 𝕜 E B p q x.1]
  exact x.2.2

/-- The restriction of a `2`-cycle of the column to the fibre, as a cocycle of the fibre. -/
noncomputable def resCyc (q : ℕ) :
    ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q) →ₗ[𝕜]
      ↥((Work.Cohomology.SSetCochainComplex 𝕜
        (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))).cycles q) where
  toFun x := Work.Cohomology.cocycleOf 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
    (resCochain 𝕜 E B p e₀ q x.1) (resCochain_cyc 𝕜 E B p e₀ q x)
  map_add' x y := by
    apply Work.Cohomology.iCycles_injective 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
    rw [map_add, Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.iCycles_cocycleOf,
      Work.Cohomology.iCycles_cocycleOf]
    exact map_add (resCochain 𝕜 E B p e₀ q)
      (x.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
      (y.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
  map_smul' c x := by
    apply Work.Cohomology.iCycles_injective 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
    rw [map_smul, Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.iCycles_cocycleOf]
    exact map_smul (resCochain 𝕜 E B p e₀ q) c
      (x.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)

/-- The underlying cochain of the restriction of a cycle is the restriction of the cycle. -/
theorem iCycles_resCyc (q : ℕ) (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q)) :
    ((Work.Cohomology.SSetCochainComplex 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))).iCycles q)
      (resCyc 𝕜 E B p e₀ q x) = resCochain 𝕜 E B p e₀ q x.1 :=
  Work.Cohomology.iCycles_cocycleOf 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
    (resCochain 𝕜 E B p e₀ q x.1) (resCochain_cyc 𝕜 E B p e₀ q x)

/-- The class of the restriction of a `2`-cycle of the column to the fibre. -/
def rhoFun (q : ℕ) :
    ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q) →ₗ[𝕜] Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q :=
  ((Work.Cohomology.SSetCochainComplex 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))).homologyπ q).hom.comp
    (resCyc 𝕜 E B p e₀ q)

/-- `rhoFun` evaluated on a cycle is the class of the restriction of the cycle. -/
theorem rhoFun_eq_class (q : ℕ) (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q)) :
    rhoFun 𝕜 E B p e₀ q x =
      Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
        (resCochain 𝕜 E B p e₀ q x.1) (resCochain_cyc 𝕜 E B p e₀ q x) :=
  rfl

/-! ## 3. The descent to the second page -/

/-- Elements of `Z_1^1` restrict to zero on the fibre. -/
theorem rhoFun_eq_zero_of_mem_pZ_one (q : ℕ) (a : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q))
    (ha : a.1 ∈ pZ 𝕜 (serreCF 𝕜 E B p) 1 1 q) :
    rhoFun 𝕜 E B p e₀ q a = 0 := by
  show ((Work.Cohomology.SSetCochainComplex 𝕜
    (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))).homologyπ q).hom
    (resCyc 𝕜 E B p e₀ q a) = 0
  rw [show resCyc 𝕜 E B p e₀ q a = 0 from by
    apply Work.Cohomology.iCycles_injective 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
    rw [iCycles_resCyc, map_zero]
    exact e2Col_coFilt_ker_res 𝕜 E B p e₀ q a.1 ha.1]
  exact map_zero _

/-- Elements of `B_2^0` are coboundaries and hence restrict to coboundaries on the fibre. -/
theorem rhoFun_eq_zero_of_mem_pB (q : ℕ) (b : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q))
    (hb : b.1 ∈ pB 𝕜 (serreCF 𝕜 E B p) 2 0 q) :
    rhoFun 𝕜 E B p e₀ q b = 0 := by
  rcases q with _ | n
  · rw [pd_pB_zero, Submodule.mem_bot] at hb
    show ((Work.Cohomology.SSetCochainComplex 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))).homologyπ 0).hom
      (resCyc 𝕜 E B p e₀ 0 b) = 0
    rw [show resCyc 𝕜 E B p e₀ 0 b = 0 from by
      apply Work.Cohomology.iCycles_injective 𝕜
        (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) 0
      rw [iCycles_resCyc, map_zero, hb]
      exact map_zero _]
    exact map_zero _
  · obtain ⟨-, y, -, hy⟩ := (pd_mem_pB_succ (𝕜 := 𝕜) (W := serreCF 𝕜 E B p)
      (r := 2) (s := 0) (n := n)).mp hb
    have hy' : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E)
        (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)
        = (b.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (n + 1)) := by
      rw [← serreCF_d_apply 𝕜 E B p n
        (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)]
      exact hy
    have hres : resCochain 𝕜 E B p e₀ (n + 1)
          (b.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (n + 1))
        = Work.Cohomology.cochainDiff 𝕜
            (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
            (resCochain 𝕜 E B p e₀ n
              (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)) := by
      rw [hy'.symm]
      exact resCochain_d 𝕜 E B p e₀ n
        (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)
    show ((Work.Cohomology.SSetCochainComplex 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))).homologyπ (n + 1)).hom
      (resCyc 𝕜 E B p e₀ (n + 1) b) = 0
    rw [show resCyc 𝕜 E B p e₀ (n + 1) b
        = (Work.Cohomology.SSetCochainComplex 𝕜
            (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))).toCycles n (n + 1)
              (resCochain 𝕜 E B p e₀ n
                (y : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n)) from by
      apply Work.Cohomology.iCycles_injective 𝕜
        (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) (n + 1)
      rw [iCycles_resCyc, Work.Cohomology.iCycles_toCycles, hres,
        Work.Cohomology.SSetCochainComplex_d_apply]]
    exact Work.Cohomology.homologyπ_toCycles 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) n (n + 1) _

/-- The denominator of `E_2^{0,q}` is killed by the restriction to the fibre. -/
theorem rhoFun_ker (q : ℕ) :
    (pDen 𝕜 (serreCF 𝕜 E B p) 2 0 q).comap (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q).subtype ≤
      (rhoFun 𝕜 E B p e₀ q).ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  rw [Submodule.mem_comap, pDen] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  have hsum_a : a + (0 : ↑((serreCF 𝕜 E B p).C.X q)) = a := add_zero a
  have hsum_b : (0 : ↑((serreCF 𝕜 E B p).C.X q)) + b = b := zero_add b
  have hX : x = (⟨a, pd_pDen_le_pZ 2 0 q (Submodule.mem_sup.mpr
        ⟨a, ha, 0, Submodule.zero_mem _, hsum_a⟩)⟩ :
        ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q)) +
      ⟨b, pd_pDen_le_pZ 2 0 q (Submodule.mem_sup.mpr
        ⟨0, Submodule.zero_mem _, b, hb, hsum_b⟩)⟩ := by
    refine Subtype.ext ?_
    show x.1 = a + b
    exact hab.symm
  rw [hX, map_add, rhoFun_eq_zero_of_mem_pZ_one 𝕜 E B p e₀ q _ ha,
    rhoFun_eq_zero_of_mem_pB 𝕜 E B p e₀ q _ hb, add_zero]

/-- The restriction-to-the-fibre map on the column `E_2^{0,q}`, descended to the second page. -/
def rho (q : ℕ) : pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 q →ₗ[𝕜]
    Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q :=
  Submodule.liftQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 q).comap
    (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q).subtype) (rhoFun 𝕜 E B p e₀ q)
    (rhoFun_ker 𝕜 E B p e₀ q)

/-- `rho` evaluated on the class of a cycle. -/
theorem rho_mkQ (q : ℕ) (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q)) :
    rho 𝕜 E B p e₀ q
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 q).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q).subtype) x)
      = Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
          (resCochain 𝕜 E B p e₀ q x.1) (resCochain_cyc 𝕜 E B p e₀ q x) := by
  rw [rho, Submodule.mkQ_apply]
  refine (LinearMap.congr_fun (Submodule.liftQ_mkQ
    (p := (pDen 𝕜 (serreCF 𝕜 E B p) 2 0 q).comap
      (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q).subtype)
    (rhoFun 𝕜 E B p e₀ q) (rhoFun_ker 𝕜 E B p e₀ q)) x).trans ?_
  exact rhoFun_eq_class 𝕜 E B p e₀ q x

/-! ## 4. `rho` is bijective -/

/-- **Injectivity of the restriction to the fibre.**  If a `2`-cycle of the column restricts to a
coboundary of the fibre then its class vanishes in `E_2^{0,q}`
(`Work.Pi6.MSS.e2Col_fibre_kernel`), and a cochain vanishes on cycles iff it is a coboundary
(`Work.Pi6.MSS.e2ColRho.classZero_vanishes`). -/
theorem rho_injective (q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) :
    Function.Injective (rho 𝕜 E B p e₀ q) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 q).comap (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q).subtype) z
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [rho_mkQ] at hz
  refine e2Col_fibre_kernel 𝕜 E B p e₀ q hfib hconn x.1 x.2 ?_
  intro γ hγ
  exact Work.Pi6.MSS.e2ColRho.classZero_vanishes 𝕜
    (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
    (resCochain 𝕜 E B p e₀ q x.1) (resCochain_cyc 𝕜 E B p e₀ q x) hz γ hγ

/-- **Surjectivity of the restriction to the fibre**, by dimensions: `E_2^{0,q}` and `H^q(F)` are
finite dimensional of the same dimension (`Work.Pi6.MSS.e2ColRho.finrank_col`) and `rho` is
injective. -/
theorem rho_surjective (N : ℕ) (q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) (hq : q ≤ N) :
    Function.Surjective (rho 𝕜 E B p e₀ q) := by
  haveI : FiniteDimensional 𝕜 (↥(pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 q)) :=
    (Work.Pi6.MSS.e2ColRho.finrank_col 𝕜 E B p e₀ N hfib hconn hfin q hq).1
  haveI : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) := hfin q hq
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  have h := LinearMap.finrank_range_add_finrank_ker (rho 𝕜 E B p e₀ q)
  rw [LinearMap.ker_eq_bot.mpr (rho_injective 𝕜 E B p e₀ q hfib hconn),
    finrank_bot, add_zero] at h
  rw [h, (Work.Pi6.MSS.e2ColRho.finrank_col 𝕜 E B p e₀ N hfib hconn hfin q hq).2]

/-- **The restriction to the fibre is an isomorphism on the column.** -/
noncomputable def rhoEquiv (N : ℕ) (q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) (hq : q ≤ N) :
    Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q ≃ₗ[𝕜]
      pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 q :=
  (LinearEquiv.ofBijective (rho 𝕜 E B p e₀ q)
    ⟨rho_injective 𝕜 E B p e₀ q hfib hconn,
      rho_surjective 𝕜 E B p e₀ N q hfib hconn hfin hq⟩).symm

/-! ## 5. Multiplicativity -/

/-- **`mssMul` at the zeroth column is `pd_mul` after normalization.** -/
theorem mssMul_norm (q q' : ℕ)
    (x : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)))
    (y : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q' : ℤ))) :
    (mssNorm 𝕜 (serreCF 𝕜 E B p) 2 0 (q + q')).hom
        (mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
          ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp) x y)
      = pCast 𝕜 (serreCF 𝕜 E B p) 2 (rfl : 0 + 0 = 0)
          (by omega : (0 + q) + (0 + q') = 0 + (q + q'))
          (pd_mul 2 0 (0 + q) 0 (0 + q')
            ((mssNorm 𝕜 (serreCF 𝕜 E B p) 2 0 q).hom x)
            ((mssNorm 𝕜 (serreCF 𝕜 E B p) 2 0 q').hom y)) := by
  obtain ⟨D⟩ := pagesData 𝕜 (serreCF 𝕜 E B p)
  rw [← pEcast_hom_apply 𝕜 (serreCF 𝕜 E B p) 2 (rfl : 0 + 0 = 0)
    (by omega : (0 + q) + (0 + q') = 0 + (q + q'))]
  rw [← mulEq 𝕜 (serreCF 𝕜 E B p) D 2 0 (0 + q) 0 (0 + q')]
  exact mssMulCompat 𝕜 (serreCF 𝕜 E B p) D 2 0 q 0 q' (by norm_num) x y

/-- The normalization `mssNorm` of a page of the zeroth column is the identity (the `ℕ`-indices
`EI (0,q)`, `EN (0,q)` are definitionally `0`, `0+q`). -/
theorem mssNorm_hom_self (q : ℕ) (x : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ))) :
    (mssNorm 𝕜 (serreCF 𝕜 E B p) 2 0 q).hom x = x := by
  rw [mssNorm_hom_apply]
  rw [pCast_congr 𝕜 (serreCF 𝕜 E B p) 2 (EI_pair 0 q)
    (rfl : EI ((0 : ℤ), (q : ℤ)) = EI ((0 : ℤ), (q : ℤ))) (EN_pair 0 q)
    (rfl : EN ((0 : ℤ), (q : ℤ)) = EN ((0 : ℤ), (q : ℤ)))]
  exact pCast_apply_self 𝕜 (serreCF 𝕜 E B p) 2 x

/-- The product of the zeroth column, expressed with the concrete page product `pd_mul`. -/
theorem mssMul_eq_pd (q q' : ℕ)
    (x : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)))
    (y : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q' : ℤ))) :
    mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
        ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp) x y
      = pCast 𝕜 (serreCF 𝕜 E B p) 2 (rfl : 0 + 0 = 0)
          (by omega : (0 + q) + (0 + q') = 0 + (q + q'))
          (pd_mul 2 0 (0 + q) 0 (0 + q') x y) := by
  simpa only [mssNorm_hom_self] using mssMul_norm 𝕜 E B p q q' x y

/-- **The restriction to the fibre is multiplicative on the column.** -/
theorem rho_pd_mul (n n' : ℕ) (X : pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 n)
    (Y : pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 n') :
    rho 𝕜 E B p e₀ (n + n') (pd_mul 2 0 n 0 n' X Y)
      = Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) n n'
          (rho 𝕜 E B p e₀ n X) (rho 𝕜 E B p e₀ n' Y) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 n).comap (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 n).subtype) X
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 n').comap (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 n').subtype) Y
  have hpf : resCochain 𝕜 E B p e₀ (n + n')
        ((pd_mulZ 2 0 n 0 n' u v).1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (n + n'))
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
          (resCochain 𝕜 E B p e₀ n (u.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n))
          (resCochain 𝕜 E B p e₀ n' (v.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n')) := by
    rw [show (pd_mulZ 2 0 n 0 n' u v).1
        = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) u.1 v.1 from ?_, resCochain_cup]
    rw [pd_mulZ_val]
    exact serreCup_apply 𝕜 p n n' u.1 v.1
  rw [pd_mul_nat, rho_mkQ, rho_mkQ, rho_mkQ]
  exact (Work.Cohomology.cohomologyClassOf_congr 𝕜
    (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) hpf
    (resCochain_cyc 𝕜 E B p e₀ (n + n') (pd_mulZ 2 0 n 0 n' u v))
    (Work.Cohomology.cochainDiff_cup_of_cocycles 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
      (resCochain 𝕜 E B p e₀ n (u.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n))
      (resCochain 𝕜 E B p e₀ n' (v.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n'))
      (resCochain_cyc 𝕜 E B p e₀ n u) (resCochain_cyc 𝕜 E B p e₀ n' v))).trans
    (Work.Cohomology.cupH'_apply' 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
      (resCochain 𝕜 E B p e₀ n (u.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n))
      (resCochain 𝕜 E B p e₀ n' (v.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n'))
      (resCochain_cyc 𝕜 E B p e₀ n u) (resCochain_cyc 𝕜 E B p e₀ n' v)).symm

/-- **`rho` on the class of a genuine cocycle is the pullback to the fibre.** -/
theorem rho_mkQ_cocycle (q : ℕ) (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q))
    (hx : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) x.1 = 0) :
    rho 𝕜 E B p e₀ q
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 q).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 q).subtype) x)
      = (cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom
          (Work.Cohomology.cohomologyClassOf 𝕜 (Work.SSS.sSing E) x.1 hx) := by
  rw [rho_mkQ]
  exact (Work.Cohomology.cohomologyClassOf_congr 𝕜
    (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) rfl _ _).trans
    (Work.Cohomology.singularCohomologyMap_classOf 𝕜
      (TopCat.ofHom (Work.StemsB.fibreIncl p (p e₀))) x.1 hx).symm

/-! ## 6. Transport of the cohomological degree of the fibre -/

/-- Transport of a fibre cohomology class along an equality of degrees. -/
def cohXcast {m k : ℕ} (h : m = k) : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) m →ₗ[𝕜]
    Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) k where
  toFun := fun x => h ▸ x
  map_add' := by subst h; intro a b; rfl
  map_smul' := by subst h; intro c a; rfl

/-- The transport of the cohomological degree, as a linear equivalence. -/
noncomputable def cohXcastEquiv {m k : ℕ} (h : m = k) :
    Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) m ≃ₗ[𝕜]
      Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) k where
  toLinearMap := cohXcast 𝕜 E B p e₀ h
  invFun := fun y => h.symm ▸ y
  left_inv := by subst h; intro x; rfl
  right_inv := by subst h; intro x; rfl

theorem cohXcast_rfl {m : ℕ} :
    cohXcast 𝕜 E B p e₀ (rfl : m = m) = LinearMap.id := by
  ext x; rfl

theorem cohXcast_comp {m k l : ℕ} (h : m = k) (h' : k = l) :
    (cohXcast 𝕜 E B p e₀ h').comp (cohXcast 𝕜 E B p e₀ h)
      = cohXcast 𝕜 E B p e₀ (h.trans h') := by
  subst h; subst h'; ext x; rfl

theorem cohXcast_comp_apply {m k l : ℕ} (h : m = k) (h' : k = l)
    (x : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) m) :
    cohXcast 𝕜 E B p e₀ h' (cohXcast 𝕜 E B p e₀ h x)
      = cohXcast 𝕜 E B p e₀ (h.trans h') x := by
  rw [← LinearMap.comp_apply, cohXcast_comp]

theorem cohXcast_congr {m k : ℕ} (h h' : m = k) :
    cohXcast 𝕜 E B p e₀ h = cohXcast 𝕜 E B p e₀ h' := by
  rw [Subsingleton.elim h h']

/-- The transport of the degree is a ring map. -/
theorem cup_cohXcast {a a' b b' : ℕ} (h₁ : a = a') (h₂ : b = b')
    (u : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) a)
    (v : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) b) :
    Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) a' b'
        (cohXcast 𝕜 E B p e₀ h₁ u) (cohXcast 𝕜 E B p e₀ h₂ v)
      = cohXcast 𝕜 E B p e₀ (show a + b = a' + b' by rw [h₁, h₂])
          (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) a b u v) := by
  subst h₁; subst h₂
  rw [cohXcast_rfl, cohXcast_rfl]
  rfl


/-- The boundary of a cochain, transported along an equality of degrees. -/
theorem resCochain_xcast {m k : ℕ} (h : m = k)
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m) :
    resCochain 𝕜 E B p e₀ k ((serreCF 𝕜 E B p).xcast h α)
      = h ▸ (resCochain 𝕜 E B p e₀ m α) := by
  subst h
  rw [CohFilt.xcast_rfl, LinearMap.id_apply]

/-- `cohXcast` is the transport along the equality of degrees. -/
theorem cohXcast_apply {m k : ℕ} (h : m = k)
    (x : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) m) :
    cohXcast 𝕜 E B p e₀ h x = h ▸ x := rfl

/-- **`rho` is compatible with the transport of the cohomological degree.** -/
theorem rho_pCast_snd {m k : ℕ} (h : m = k) (x : pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 m) :
    rho 𝕜 E B p e₀ k (pCast 𝕜 (serreCF 𝕜 E B p) 2 (rfl : 0 = 0) h x)
      = cohXcast 𝕜 E B p e₀ h (rho 𝕜 E B p e₀ m x) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 m).comap (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 m).subtype) x
  have hpc : pCast 𝕜 (serreCF 𝕜 E B p) 2 (rfl : 0 = 0) h
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 m).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 m).subtype) u)
      = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 k).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 k).subtype)
          ⟨(serreCF 𝕜 E B p).xcast h u.1, pd_pZ_xcast (rfl : 0 = 0) h u.2⟩ := by
    rw [← pEcast_hom_apply 𝕜 (serreCF 𝕜 E B p) 2 (rfl : 0 = 0) h]
    exact pd_pEcast_mkQ' (𝕜 := 𝕜) (W := serreCF 𝕜 E B p) (r := 2) (rfl : 0 = 0) h u
  rw [hpc, rho_mkQ, rho_mkQ, cohXcast_apply]
  refine (Work.Cohomology.cohomologyClassOf_congr 𝕜
    (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
    (resCochain_xcast 𝕜 E B p e₀ h (u.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m)) _ _).trans
    (Work.Cohomology.cohomologyClassOf_cast 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) h
      (resCochain 𝕜 E B p e₀ m (u.1 : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m))
      (resCochain_cyc 𝕜 E B p e₀ m u)).symm

/-! ## 7. The zeroth column as a module over the fibre cohomology -/

/-- **The zeroth column of `E_2`, identified with the cohomology of the fibre** by the restriction
map (with the degree transport `0 + q = q`). -/
noncomputable def rhoSSEquiv (N : ℕ) (q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) (hq : q ≤ N) :
    mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ≃ₗ[𝕜]
      Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q :=
  (rhoEquiv 𝕜 E B p e₀ N (0 + q) hfib hconn hfin (by omega)).symm.trans
    (cohXcastEquiv 𝕜 E B p e₀ (Nat.zero_add q))

/-- `rhoSSEquiv` is the restriction to the fibre, transported to the degree `q`. -/
theorem rhoSSEquiv_apply (N q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) (hq : q ≤ N)
    (x : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ))) :
    rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq x =
      cohXcast 𝕜 E B p e₀ (Nat.zero_add q) (rho 𝕜 E B p e₀ (0 + q) x) :=
  rfl

/-- **The restriction to the fibre is a ring map on the zeroth column.** -/
theorem rhoSSEquiv_mul (N q q' : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (hq : q ≤ N) (hq' : q' ≤ N) (hqq : q + q' ≤ N)
    (x : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)))
    (y : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q' : ℤ))) :
    rhoSSEquiv 𝕜 E B p e₀ N (q + q') hfib hconn hfin hqq
        (mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
          ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp) x y)
      = Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q'
          (rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq x)
          (rhoSSEquiv 𝕜 E B p e₀ N q' hfib hconn hfin hq' y) := by
  rw [rhoSSEquiv_apply, rhoSSEquiv_apply, rhoSSEquiv_apply, mssMul_eq_pd, rho_pCast_snd,
    rho_pd_mul, cohXcast_comp_apply]
  rw [cup_cohXcast]

/-! ## 8. The fibre-edge (clause 3) machinery -/

/-- A cocycle of `E` survives to the column `E_{q+2}^{0,q}`. -/
theorem mem_pZ_of_cocycle (q : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (hα : Work.Cohomology.cochainDiff 𝕜 (Work.SSS.sSing E) α = 0) :
    α ∈ pZ 𝕜 (serreCF 𝕜 E B p) (q + 2) 0 q := by
  refine ⟨?_, ?_⟩
  · rw [(serreCF 𝕜 E B p).F_zero q]
    exact Submodule.mem_top
  · show (serreCF 𝕜 E B p).d q α ∈ (serreCF 𝕜 E B p).F (0 + (q + 2)) (q + 1)
    rw [show (serreCF 𝕜 E B p).F (0 + (q + 2)) (q + 1) = ⊥ from by
        rw [show 0 + (q + 2) = (q + 1) + 1 from by omega]
        exact (serreCF 𝕜 E B p).F_top (q + 1),
      Submodule.mem_bot, serreCF_d_apply 𝕜 E B p q α]
    exact hα

/-- The iterated zeroth-column inclusion is the inclusion of subquotients on classes. -/
theorem mssColIter_mkQ (q k : ℕ)
    (w : ↥(pZ 𝕜 (serreCF 𝕜 E B p) (k + 2) (EI ((0 : ℤ), (q : ℤ)))
      (EN ((0 : ℤ), (q : ℤ))))) :
    mssColIter 𝕜 E B p q k
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (k + 2) (EI ((0 : ℤ), (q : ℤ)))
          (EN ((0 : ℤ), (q : ℤ)))).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) (k + 2) (EI ((0 : ℤ), (q : ℤ)))
            (EN ((0 : ℤ), (q : ℤ)))).subtype) w)
      = Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 (EI ((0 : ℤ), (q : ℤ)))
          (EN ((0 : ℤ), (q : ℤ)))).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 2 (EI ((0 : ℤ), (q : ℤ)))
            (EN ((0 : ℤ), (q : ℤ)))).subtype)
          ⟨w.1, pd_pZ_anti (by omega) le_rfl w.2⟩ := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show (mssColIter 𝕜 E B p q n)
        ((mssCol 𝕜 (serreCF 𝕜 E B p) (n + 2) (q : ℤ))
          (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) (n + 3)
            (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ)))).comap
              (pZ 𝕜 (serreCF 𝕜 E B p) (n + 3) (EI ((0 : ℤ), (q : ℤ)))
                (EN ((0 : ℤ), (q : ℤ)))).subtype) w)) = _
      rw [Work.Pi6.MSS.e2ColRho.mssCol_mkQ (𝕜 := 𝕜) (W := serreCF 𝕜 E B p)
        (r := n + 2) (hr := by omega) (q := q)]
      exact ih (pd_cycR (n + 2) (EI ((0 : ℤ), (q : ℤ))) (EN ((0 : ℤ), (q : ℤ))) w)

/-! ## 9. The unit of the page -/

/-- The restriction of the unit cochain of `E` is the unit cochain of the fibre. -/
theorem resCochain_unitCochain :
    resCochain 𝕜 E B p e₀ 0 (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E))
      = Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_resCochain, Work.Cohomology.genEval_unitCochain,
    Work.Cohomology.genEval_unitCochain]

/-- The unit cochain of `E` is a `2`-cycle of the column. -/
theorem mem_pZ_unitCochain :
    Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E) ∈
      pZ 𝕜 (serreCF 𝕜 E B p) 2 0 0 :=
  mem_pZ_of_cocycle 𝕜 E B p 0 _
    (Work.Cohomology.cochainDiff_unitCochain 𝕜 (Work.SSS.sSing E))

/-- The class of the unit cochain in `E_2^{0,0}`. -/
noncomputable def e2ColUnit : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (0 : ℤ)) :=
  Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 2 0 0).comap
    (pZ 𝕜 (serreCF 𝕜 E B p) 2 0 0).subtype)
    ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E), mem_pZ_unitCochain 𝕜 E B p⟩

/-- The class of the unit cochain is the multiplicative unit of the second page. -/
theorem e2ColUnit_pageUnit : mssPageUnit 𝕜 E B p (e2ColUnit 𝕜 E B p) :=
  pageUnitSpec 𝕜 E B p (mem_pZ_unitCochain 𝕜 E B p)

/-- The restriction to the fibre sends the unit of the column to the unit of `H^0(F)`. -/
theorem rho_e2ColUnit :
    rho 𝕜 E B p e₀ 0 (e2ColUnit 𝕜 E B p)
      = Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)) := by
  rw [e2ColUnit, rho_mkQ]
  exact (Work.Cohomology.cohomologyClassOf_congr 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))
      (resCochain_unitCochain 𝕜 E B p e₀)
      _
      (Work.Cohomology.cochainDiff_unitCochain 𝕜
        (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))))).trans
    (Work.Cohomology.cohomologyClassOf_congr 𝕜
      (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) rfl
      (Work.Cohomology.cochainDiff_unitCochain 𝕜
        (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))))
      (Work.Cohomology.cochainDiff_unitCochain 𝕜
        (Work.SSS.sSing (Work.StemsB.fibre p (p e₀)))))

/-- The restriction to the fibre sends the unit of the column to the unit of `H^0(F)`
(bidegree form). -/
theorem rhoSSEquiv_e2ColUnit (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    rhoSSEquiv 𝕜 E B p e₀ N 0 hfib hconn hfin (Nat.zero_le N) (e2ColUnit 𝕜 E B p)
      = Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)) := by
  rw [rhoSSEquiv_apply, rho_e2ColUnit]
  rw [show cohXcast 𝕜 E B p e₀ (Nat.zero_add 0)
        (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))
      = Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)) from by
    rw [cohXcast_congr 𝕜 E B p e₀ (Nat.zero_add 0) (rfl : 0 + 0 = 0), cohXcast_rfl]
    rfl]

/-- **The unit clause**: the inverse of the restriction to the fibre sends the unit of `H^0(F)` to
the multiplicative unit of the page. -/
theorem colUnit_pageUnit (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    mssPageUnit 𝕜 E B p
      ((rhoSSEquiv 𝕜 E B p e₀ N 0 hfib hconn hfin (Nat.zero_le N)).symm
        (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) := by
  rw [← rhoSSEquiv_e2ColUnit 𝕜 E B p e₀ N hfib hconn hfin,
    LinearEquiv.symm_apply_apply]
  exact e2ColUnit_pageUnit 𝕜 E B p


end

end Work.Pi6.MSS
