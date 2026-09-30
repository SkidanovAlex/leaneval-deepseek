import Mathlib
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.e2Row_exists
import Submission.Work.Pi6.MSS.assemble
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.pageUnitSpec
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSS.e2Col_exists
import Submission.Work.Pi6.MSS.e2Add
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The candidate inverse `Ψ` of the `E_2` identification: `b ⊗ f ↦ row b · col f`. -/
noncomputable def e2Psi (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (e₀ : E)
    (row : ∀ s : ℕ, Work.Pi6.Coh 𝕜 B s →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)))
    (col : ∀ q : ℕ, Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)))
    (s q : ℕ) :
    (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (q : ℤ)) :=
  TensorProduct.lift (LinearMap.mk₂ 𝕜
    (fun b f => mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
      ((s : ℤ), (q : ℤ)) (by ext <;> simp) (row s b) (col q f))
    (fun b1 b2 f => by simp only [map_add, LinearMap.add_apply])
    (fun a b f => by simp only [map_smul, LinearMap.smul_apply])
    (fun b f1 f2 => by simp only [map_add, LinearMap.add_apply])
    (fun a b f => by simp only [map_smul, LinearMap.smul_apply]))

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The value of `Ψ` on a pure tensor. -/
@[simp] theorem e2Psi_tmul (p : C(E, B)) (e₀ : E)
    (row : ∀ s : ℕ, Work.Pi6.Coh 𝕜 B s →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)))
    (col : ∀ q : ℕ, Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)))
    (s q : ℕ) (b : Work.Pi6.Coh 𝕜 B s)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    e2Psi 𝕜 E B p e₀ row col s q (b ⊗ₜ[𝕜] f) =
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
        ((s : ℤ), (q : ℤ)) (by ext <;> simp) (row s b) (col q f) :=
  rfl


/-- The concrete base row map of `e2Row_exists`, as a self-contained definition. -/
noncomputable def e2Row (p : C(E, B)) (s : ℕ) :
    Work.Pi6.Coh 𝕜 B s →ₗ[𝕜] mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) :=
  rowMap 𝕜 p s (ker_clsB_le_ker_Rb 𝕜 p s) (clsB_range_top 𝕜 B s)



/-- The column map of `e2Col_exists` (the inverse of the restriction to the fibre) extended to all
degrees (junk, namely `0`, above `N`). -/
noncomputable def e2ColAll (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    ∀ q : ℕ, Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) :=
  fun q => if h : q ≤ N then
    (rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin h).symm.toLinearMap
  else 0

/-- The computation rule for `e2ColAll`. -/
theorem e2ColAll_apply (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (q : ℕ) (hq : q ≤ N) :
    e2ColAll 𝕜 p e₀ N hfib hconn hfin q =
      (rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm.toLinearMap :=
  dif_pos hq

/-- The unit clause for `e2ColAll` (degree `0`). -/
theorem e2ColAll_pageUnit (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    mssPageUnit 𝕜 E B p
      (e2ColAll 𝕜 p e₀ N hfib hconn hfin 0 (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) := by
  rw [e2ColAll_apply 𝕜 p e₀ N hfib hconn hfin 0 (Nat.zero_le N)]
  exact colUnit_pageUnit 𝕜 E B p e₀ N hfib hconn hfin

/-- The multiplicativity clause for `e2ColAll`, in degrees with `q + q' ≤ N`. -/
theorem e2ColAll_mul (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (q q' : ℕ) (hq : q ≤ N) (hq' : q' ≤ N) (hqq : q + q' ≤ N)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (f' : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q') :
    e2ColAll 𝕜 p e₀ N hfib hconn hfin (q + q')
        (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f') =
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
        ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
        (e2ColAll 𝕜 p e₀ N hfib hconn hfin q f)
        (e2ColAll 𝕜 p e₀ N hfib hconn hfin q' f') := by
  rw [e2ColAll_apply 𝕜 p e₀ N hfib hconn hfin (q + q') hqq,
    e2ColAll_apply 𝕜 p e₀ N hfib hconn hfin q hq,
    e2ColAll_apply 𝕜 p e₀ N hfib hconn hfin q' hq']
  change (rhoSSEquiv 𝕜 E B p e₀ N (q + q') hfib hconn hfin hqq).symm
      (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f') =
    mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
      ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
      ((rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm f)
      ((rhoSSEquiv 𝕜 E B p e₀ N q' hfib hconn hfin hq').symm f')
  rw [LinearEquiv.symm_apply_eq,
    rhoSSEquiv_mul 𝕜 E B p e₀ N q q' hfib hconn hfin hq hq' hqq,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The fibre-edge clause for `e2ColAll`, in degrees `q ≤ N`. -/
theorem e2ColAll_edge (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (q : ℕ) (hq : q ≤ N) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    (∃ e : Work.Pi6.Coh 𝕜 E q,
        (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f) ↔
      ∃ z : mssE 𝕜 (serreCF 𝕜 E B p) (q + 2) ((0 : ℤ), (q : ℤ)),
        mssColIter 𝕜 E B p q q z = e2ColAll 𝕜 p e₀ N hfib hconn hfin q f := by
  rw [e2ColAll_apply 𝕜 p e₀ N hfib hconn hfin q hq]
  exact Work.Pi6.MSS.e2ColRho.mem_range_col_iff 𝕜 E B p e₀ N q hfib hconn hfin hq f
/-- **The main argument of `e2Mul`.** -/
theorem e2Mul_of (p : C(E, B)) (e₀ : E) (N : ℕ)
    (D : PagesData 𝕜 (serreCF 𝕜 E B p))
    (col : ∀ q : ℕ, Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)))
    (hcol_unit : mssPageUnit 𝕜 E B p
      (col 0 (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))))
    (hrow_unit : mssPageUnit 𝕜 E B p (e2Row 𝕜 p 0 (Work.Pi6.one 𝕜 B)))
    (hkoszul : ∀ (s q s' q' : ℕ), s + s' ≤ N → q + q' ≤ N →
      ∀ (b : Work.Pi6.Coh 𝕜 B s)
      (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
      (b' : Work.Pi6.Coh 𝕜 B s') (f' : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q'),
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
          (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
          (mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
            ((s : ℤ), (q : ℤ)) (by ext <;> simp) (e2Row 𝕜 p s b) (col q f))
          (mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s' : ℤ), (0 : ℤ)) ((0 : ℤ), (q' : ℤ))
            ((s' : ℤ), (q' : ℤ)) (by ext <;> simp) (e2Row 𝕜 p s' b') (col q' f'))
        = (-1 : 𝕜) ^ (q * s') •
          mssMul 𝕜 (serreCF 𝕜 E B p) 2 (((s + s' : ℕ) : ℤ), (0 : ℤ))
            ((0 : ℤ), ((q + q' : ℕ) : ℤ))
            (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
            (e2Row 𝕜 p (s + s') (Work.Pi6.cup 𝕜 B s s' b b'))
            (col (q + q') (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f')))
    (hbij : ∀ (s q : ℕ), s ≤ N → q ≤ N →
      Function.Bijective (e2Psi 𝕜 E B p e₀ (e2Row 𝕜 p) col s q))
    (hcol_edge : ∀ (q : ℕ), q ≤ N → ∀ f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q,
      (∃ e : Work.Pi6.Coh 𝕜 E q,
          (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f) ↔
        ∃ z : mssE 𝕜 (serreCF 𝕜 E B p) (q + 2) ((0 : ℤ), (q : ℤ)),
          mssColIter 𝕜 E B p q q z = col q f)
    (hrow_edge : ∀ (s : ℕ) (b : Work.Pi6.Coh 𝕜 B s),
      mssBotIter 𝕜 E B p s s (e2Row 𝕜 p s b) = 0 ↔ (Work.Pi6.cmap 𝕜 p s).hom b = 0) :
    ∃ e2 : ∀ (s q : ℕ), s ≤ N → q ≤ N →
        ((mssSS 𝕜 (serreCF 𝕜 E B p) D).E 2 ((s : ℤ), (q : ℤ)) ≅
          ModuleCat.of 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
            (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))),
      (∀ (s q s' q' : ℕ) (hs : s ≤ N) (hq : q ≤ N) (hs' : s' ≤ N) (hq' : q' ≤ N)
        (b : Work.Pi6.Coh 𝕜 B s) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
        (b' : Work.Pi6.Coh 𝕜 B s') (f' : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q')
        (hss : s + s' ≤ N) (hqq : q + q' ≤ N),
        (mssSS 𝕜 (serreCF 𝕜 E B p) D).mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
            (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
            ((e2 s q hs hq).inv.hom (b ⊗ₜ f)) ((e2 s' q' hs' hq').inv.hom (b' ⊗ₜ f'))
          = ((-1 : 𝕜) ^ (q * s')) • (e2 (s + s') (q + q') (by omega) (by omega)).inv.hom
              ((Work.Pi6.cup 𝕜 B s s' b b') ⊗ₜ
                (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f'))) ∧
      (∀ (s : ℕ) (hs : s ≤ N) (b : Work.Pi6.Coh 𝕜 B s),
        ((mssSS 𝕜 (serreCF 𝕜 E B p) D).botTo (s : ℤ) s).hom
            ((e2 s 0 (by omega) (by omega)).inv.hom
              (b ⊗ₜ Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) = 0 ↔
          (Work.Pi6.cmap 𝕜 p s).hom b = 0) ∧
      (∀ (q : ℕ) (hq : q ≤ N) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q),
        (∃ e : Work.Pi6.Coh 𝕜 E q,
            (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f) ↔
          ∃ z : (mssSS 𝕜 (serreCF 𝕜 E B p) D).E (q + 2) ((0 : ℤ), (q : ℤ)),
            ((mssSS 𝕜 (serreCF 𝕜 E B p) D).colTo (q : ℤ) q).hom z =
              (e2 0 q (by omega) (by omega)).inv.hom
                (Work.Pi6.one 𝕜 B ⊗ₜ f)) := by
  classical
  let e2 : ∀ (s q : ℕ), s ≤ N → q ≤ N →
      ((mssSS 𝕜 (serreCF 𝕜 E B p) D).E 2 ((s : ℤ), (q : ℤ)) ≅
        ModuleCat.of 𝕜 (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
          (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))) :=
    fun s q hs hq => LinearEquiv.toModuleIso
      (LinearEquiv.ofBijective (e2Psi 𝕜 E B p e₀ (e2Row 𝕜 p) col s q) (hbij s q hs hq)).symm
  have key : ∀ (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N)
      (x : TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)),
      (e2 s q hs hq).inv.hom x = e2Psi 𝕜 E B p e₀ (e2Row 𝕜 p) col s q x :=
    fun s q hs hq x => rfl
  refine ⟨e2, ?_, ?_, ?_⟩
  · intro s q s' q' hs hq hs' hq' b f b' f' hss hqq
    rw [key s q hs hq (b ⊗ₜ[𝕜] f), key s' q' hs' hq' (b' ⊗ₜ[𝕜] f'),
      key (s + s') (q + q') (by omega) (by omega) ((Work.Pi6.cup 𝕜 B s s' b b') ⊗ₜ[𝕜]
        (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f'))]
    rw [E2Aux.mssSS_mul_apply]
    simp only [e2Psi_tmul]
    exact hkoszul s q s' q' hss hqq b f b' f'
  · intro s hs b
    rw [key s 0 hs (by omega) (b ⊗ₜ[𝕜] Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀))),
      e2Psi_tmul]
    rw [E2Aux.botTo_eq_mssBotIter]
    have hunit : mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), ((0 : ℕ) : ℤ))
        ((s : ℤ), ((0 : ℕ) : ℤ)) (by ext <;> simp) (e2Row 𝕜 p s b)
        (col 0 (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) = e2Row 𝕜 p s b := by
      simpa using hcol_unit.2 s 0 (e2Row 𝕜 p s b)
    rw [hunit]
    exact hrow_edge s b
  · intro q hq f
    rw [key 0 q (by omega) hq (Work.Pi6.one 𝕜 B ⊗ₜ[𝕜] f), e2Psi_tmul]
    rw [E2Aux.colTo_eq_mssColIter]
    have hunit : mssMul 𝕜 (serreCF 𝕜 E B p) 2 (((0 : ℕ) : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
        (((0 : ℕ) : ℤ), (q : ℤ)) (by ext <;> simp) (e2Row 𝕜 p 0 (Work.Pi6.one 𝕜 B))
        (col q f) = col q f := by
      simpa using hrow_unit.1 0 q (col q f)
    rw [hunit]
    exact hcol_edge q hq f



end

end Work.Pi6.MSS

namespace Work.Pi6

namespace One

/-- Compatibility alias for the historical spelling `Work.Pi6.One.one` of the unit class
`Work.Pi6.one` (the notation used in the statement of `Work.Pi6.MSS.e2Mul`). -/
noncomputable abbrev one (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] : Coh R X 0 :=
  Work.Pi6.one R X

end One

end Work.Pi6
