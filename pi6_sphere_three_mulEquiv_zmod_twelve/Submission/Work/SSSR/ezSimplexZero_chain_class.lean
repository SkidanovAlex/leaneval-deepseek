import Mathlib
import Submission.Work.SSSR.serreE1D1
import Submission.Work.SSSR.serreE1EZ
import Submission.Work.SSSR.serreE1PieceExplicit
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.SSSR.ezGen_snd_sum_zero
import Submission.Work.SSSR.piszDefs
import Submission.Work.SSSR.iotaF_chainMap
import Submission.Work.SSSR.ezLinSnd_map_fst
import Submission.Work.SSSR.sSing_fibre_factor
import Submission.Work.SSSR.sigmaVert_app_ssetVertex
import Submission.Work.SSSR.pieceIso_lift_chain
import Submission.Work.SSSR.vertRestrTransportChains
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

/-- **The defining property of the trivialisation `Work.SSSR.triv`.**  For every path `γ : b → b'`,
the canonical fibre transport along `γ` followed by `triv b'` is `triv b`. -/
lemma triv_transport {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) {b b' : B} (γ : Path b b') :
    Work.SSSR.transportIsoPath p hfib γ t ≪≫ Work.SSSR.triv p e₀ hfib hc t b'
      = Work.SSSR.triv (R := R) p e₀ hfib hc t b :=
  (Classical.choose_spec (Work.SSSR.fibreTrivializationOfSimplyConn p (p e₀) t
    (fun {b b'} γ => Work.SSSR.transportIsoPath p hfib γ t)
    (fun γ δ => Work.SSSR.transportIsoPath_trans p hfib t γ δ)
    (fun γ γ' H => Work.SSSR.transportIsoPath_homotopic p hfib t γ γ' H) hc)) γ


/-! ## Elementary homology lemmas (local copies of the ones in
`Submission/Work/SSS/pieceIso_ezSimplexZero.lean`, which cannot be imported here: that module
depends on the still-`sorry`ed `Work.SSSR.vertRestr_transport`.) -/

/-- The differential of the induced chain map, elementwise. -/
lemma pEZ_sCCMap_d_applyA {X Y : SSet.{0}} (g : X ⟶ Y) (i j : ℕ) (x : (sCC R X).X i) :
    (sCC R Y).d i j ((sCCMap R g).f i x) = (sCCMap R g).f j ((sCC R X).d i j x) := by
  have h := congrArg (fun (g : (sCC R X).X i ⟶ (sCC R Y).X j) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm (sCCMap R g) i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- `homologyπ` is natural with respect to `homologyMap`. -/
lemma pEZ_homologyπ_map {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (i : ℕ)
    (x : K.cycles i) :
    (L.homologyπ i) ((HomologicalComplex.cyclesMap φ i) x)
      = (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) x) :=
  (congrArg (fun (f : K.cycles i ⟶ L.homology i) => f x)
    (HomologicalComplex.homologyπ_naturality φ i)).symm

/-- The `iCycles` inclusion of a `cyclesMk`. -/
lemma pEZ_iCycles_cyclesMk {K : ChainComplex (ModuleCat R) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : ((forget₂ (ModuleCat R) Ab).map (K.d i j)) x = 0) :
    (ConcreteCategory.hom (K.iCycles i)) (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

/-- `cyclesMap` on a `cyclesMk`. -/
lemma pEZ_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : (ModuleCat.Hom.hom (K.d i j)) x = 0)
    (hx' : (ModuleCat.Hom.hom (L.d i j)) ((φ.f i) x) = 0) :
    (HomologicalComplex.cyclesMap φ i) (K.cyclesMk x j hj hx) = L.cyclesMk ((φ.f i) x) j hj hx' := by
  apply (Preadditive.mono_iff_injective (L.iCycles i)).1 inferInstance
  show (ConcreteCategory.hom (L.iCycles i))
      ((ConcreteCategory.hom (HomologicalComplex.cyclesMap φ i)) (K.cyclesMk x j hj hx))
    = (ConcreteCategory.hom (L.iCycles i)) (L.cyclesMk ((φ.f i) x) j hj hx')
  have hmap := congrArg (fun (f : K.cycles i ⟶ L.X i) =>
    (ConcreteCategory.hom f) (K.cyclesMk x j hj hx)) (HomologicalComplex.cyclesMap_i φ i)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hmap
  rw [hmap, pEZ_iCycles_cyclesMk hj x hx, pEZ_iCycles_cyclesMk hj ((φ.f i) x) hx']

/-- `homologyπ` of the image of a cycle, as a `homologyMap`. -/
lemma pEZ_homologyπ_sCCMap_cyclesMk {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : (ModuleCat.Hom.hom (K.d i j)) x = 0)
    (hx' : (ModuleCat.Hom.hom (L.d i j)) ((φ.f i) x) = 0) :
    (L.homologyπ i) (L.cyclesMk ((φ.f i) x) j hj hx')
      = (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) (K.cyclesMk x j hj hx)) := by
  rw [← pEZ_cyclesMap_cyclesMk φ hj x hx hx']
  exact pEZ_homologyπ_map φ i (K.cyclesMk x j hj hx)

/-- An isomorphism of modules is injective on elements. -/
lemma pEZ_iso_hom_injective {A B : ModuleCat R} (e : A ≅ B) : Function.Injective e.hom := by
  intro a b hab
  have h := congrArg (fun z => e.inv.hom z) hab
  simpa only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id,
    LinearMap.id_apply] using h

/-- The chain map induced by the identity is the identity. -/
lemma pEZ_sCCMap_id (X : SSet.{0}) : sCCMap R (𝟙 X) = 𝟙 (sCC R X) := by
  simp [sCCMap]

/-- **Transport comparison of `triv`-equivalent fibre classes.**  If two fibre homology classes
have the same image under the trivialisation `triv`, they correspond under the canonical transport
along any path between the base points. -/
lemma pEZ_transport_eq_of_triv {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (t : ℕ) {b b' : B} (γ : Path b b')
    (z : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) t)
    (z' : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b') t)
    (hm : (Work.SSSR.triv p e₀ hfib hc t b').hom z'
      = (Work.SSSR.triv p e₀ hfib hc t b).hom z) :
    (Work.SSSR.transportIsoPath p hfib γ t).hom z = z' := by
  have hnat : (Work.SSSR.triv p e₀ hfib hc t b').hom
      ((Work.SSSR.transportIsoPath p hfib γ t).hom z)
      = (Work.SSSR.triv p e₀ hfib hc t b).hom z := by
    have h := triv_transport (R := R) p e₀ hfib hc t γ
    exact congrArg (fun (e : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b) t ≅ Work.SSSR.coefM p e₀ t)
      => e.hom z) h
  exact pEZ_iso_hom_injective (Work.SSSR.triv p e₀ hfib hc t b') (by rw [hnat, ← hm])

/-- The sign `c_P = (-1)^{P(P+1)/2}` of the tower comparison, defined recursively. -/
def ezccSign : ℕ → ℤ :=
  fun n => Nat.rec 1 (fun k acc => ((-1 : ℤ) ^ (k+1)) * acc) n

@[simp] lemma ezccSign_zero : ezccSign 0 = 1 := rfl

lemma ezccSign_succ (n : ℕ) : ezccSign (n+1) = ((-1 : ℤ) ^ (n+1)) * ezccSign n := rfl

/-- **The `0`-face collapse, for arbitrary cycles.**  With `σ : Δ[s+1] ⟶ Sing B`, `b = σ(v₀)`,
`b' = σ(v₁) = sigmaVert (δ 0 ≫ σ)`, a cycle chain `z` of the fibre over `b` and a cycle chain `z'`
of the fibre over `b'` whose `triv`-classes agree, the class of the `0`-face lift
`(ezSimplexZero)_* EZ(std_s, z)` in the `(δ 0 ≫ σ)`-piece equals the class of the canonical lift
`(ezSimplex_{δ 0 ≫ σ})_* EZ(std_s, z')`.

This is the `i = 0` input of the computation of `d¹` (the only face whose base point moves, cf.
`REFS/NOTES_LEAD_SSS_d1.md` §4.2 and `REFS/NOTES_SESSION5.md` §(3)).  It is the CHAIN-level (hence
non-vacuous) form of `Work.SSSR.pieceIso_ezSimplexZero`: for a simplex of even degree `≥ 2` the
hypothesis `∂τ = 0` is unsatisfiable, so the simplex-level statement says nothing in those
degrees.  Equivalently (`(ε_{δ 0 ≫ σ})` being an isomorphism) the iterated last-face connecting
map sends `[K]` to `c s` times the `triv`-transport of `[z]`.

Route.  `cases s`; for `s = 0` the statement is that the `v₁`-vertex restriction `vres` of the
coherent lift `liftFam p hfib 1 b (σ)` (the base point of `δ 0 ≫ σ` is `σ(v₁)`, and
`Δ[0] ⊗ F_b ≅ F_b`) induces the same map on homology as the canonical transport
`transportIsoPath p hfib γ`, i.e. `Work.SSSR.transport_eq_topEnd` combined with
`Work.SSSR.fibreTrivializationOfSimplyConn`'s defining property of `triv`; for `s+1` peel the last
face exactly as in the proof of `Work.SSSR.serreE1PieceIso_iota_step`
(`Work.SSSR.iotaTBdryHorn`, `Work.SSSR.pieceBdryHornIsoIso`) — the only new ingredient is that the
`i = 0` face keeps `ezSimplexZero`, for which the base case applies after transporting.
The helpers `hK`, `hL` (that the two chains are cycles in the piece) follow from the linearised
Eilenberg–Zilber boundary formula `Work.SSSR.ezLinSnd_boundary` and `hz`, `hz'`; the prover should
add them as local lemmas of the same file if useful. -/
theorem ezSimplexZero_chain_class {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hc : Work.SSSR.PiS.SimplyConn B (p e₀)) (s t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ Work.SSSR.sSing B)
    (h : Work.SSSR.sigmaVert σ = b)
    (z : (Work.SSSR.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (z' : (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).X t)
    (hz' : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC p
              (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).d t
              ((ComplexShape.down ℕ).next t))) z' = 0)
    (hK : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).d (s+t) ((ComplexShape.down ℕ).next (s+t))))
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplexZero p
              (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b σ h)).f (s+t)))
              (Work.SSSR.ezLinSnd s t
                (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex s) z))) = 0)
    (hL : (ModuleCat.Hom.hom ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).d (s+t) ((ComplexShape.down ℕ).next (s+t))))
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p
              (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
              (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)).f (s+t)))
              (Work.SSSR.ezLinSnd s t
                (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
                  (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
                (Work.SSSR.stdIdSimplex s) z'))) = 0)
    (hm : (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t
            (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).hom)
          ((Work.SSSR.fibreCC p
              (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).homologyπ t
            ((Work.SSSR.fibreCC p
                (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).cyclesMk z'
              ((ComplexShape.down ℕ).next t) rfl hz'))
        = (ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hc t b).hom)
            ((Work.SSSR.fibreCC p b).homologyπ t
              ((Work.SSSR.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))) :
    (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).homologyπ (s+t)
        ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
            ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplexZero p
              (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b σ h)).f (s+t)))
              (Work.SSSR.ezLinSnd s t
                (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex s) z)))
          ((ComplexShape.down ℕ).next (s+t)) rfl hK)
      = (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
          (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).homologyπ (s+t)
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p
                (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
                (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
                (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)).f (s+t)))
                (Work.SSSR.ezLinSnd s t
                  (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                  (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
                    (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
                  (Work.SSSR.stdIdSimplex s) z')))
            ((ComplexShape.down ℕ).next (s+t)) rfl hL) := by
  -- ## Step 1: the vertex-`1` restriction `vL` of the `0`-face lift
  have hE : Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b σ h
      ≫ pullback.snd (SSet.stdSimplex.δ (n := s) 0 ≫ σ) (Work.SSSR.sSingP p)
      = (SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)))
        ≫ Work.SSSR.liftFam p hfib (s+1) b σ h := by
    rw [Work.SSSR.ezSimplexZero_snd, Category.assoc, Work.SSSR.ezSimplex_snd]
  have hLP : ((SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)))
        ≫ Work.SSSR.liftFam p hfib (s+1) b σ h) ≫ Work.SSSR.sSingP p
      = SemiCartesianMonoidalCategory.fst (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
          (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) ≫ (SSet.stdSimplex.δ (n := s) 0 ≫ σ) := by
    rw [Category.assoc, Work.SSSR.liftFam_proj, ← Category.assoc,
      CartesianMonoidalCategory.tensorHom_fst, Category.assoc]
  have hwconst : (Work.SSSR.vertIncl p b s
        ≫ Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b σ h
        ≫ pullback.snd (SSet.stdSimplex.δ (n := s) 0 ≫ σ) (Work.SSSR.sSingP p))
        ≫ Work.SSSR.sSingP p
      = SSet.const (TopCat.toSSetObj₀Equiv.symm
          (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))) := by
    rw [hE]
    rw [Category.assoc]
    rw [hLP]
    rw [← Category.assoc]
    rw [Work.SSSR.vertIncl_fst]
    rw [SSet.const_comp]
    congr 1
    rw [Equiv.eq_symm_apply]
    exact Work.SSSR.sigmaVert_app_ssetVertex (SSet.stdSimplex.δ (n := s) 0 ≫ σ)
  obtain ⟨vL, hvL⟩ := Work.SSSR.sSing_fibre_factor p
      (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
      (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b))
      (Work.SSSR.vertIncl p b s ≫ Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib)
        (Work.SSSR.liftFam_proj p hfib) s b σ h
        ≫ pullback.snd (SSet.stdSimplex.δ (n := s) 0 ≫ σ) (Work.SSSR.sSingP p)) hwconst
  -- ## Step 2: the cycle conditions of the two towers
  have hcycR' : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))).d t
      ((ComplexShape.down ℕ).next t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))))).f t)) (z')) = 0 := by
    simpa using hz'
  have hcycL' : (ModuleCat.Hom.hom ((Work.SSSR.sCC R (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))).d t
      ((ComplexShape.down ℕ).next t)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R vL).f t)) (z)) = 0 := by
    rw [Work.SSSR.pEZ_sCCMap_d_applyA vL t ((ComplexShape.down ℕ).next t) z, hz]
    simp
  -- ## Step 3: the two tower comparisons
  have hR := Work.SSSR.pieceIso_lift_chain p hfib Work.SSSR.ezccSign Work.SSSR.ezccSign_zero
      Work.SSSR.ezccSign_succ s t (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ σ)
      (Work.SSSR.ezSimplex p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)
      (Work.SSSR.ezSimplex_fst _ _ _ _ _ _)
      (𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))))
      (by rw [Category.id_comp, Work.SSSR.ezSimplex_snd, Work.SSSR.liftFam_vert])
      z' hz' hL hcycR'
  have hL' := Work.SSSR.pieceIso_lift_chain p hfib Work.SSSR.ezccSign Work.SSSR.ezccSign_zero
      Work.SSSR.ezccSign_succ s t b (SSet.stdSimplex.δ (n := s) 0 ≫ σ)
      (Work.SSSR.ezSimplexZero p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b σ h)
      (Work.SSSR.ezSimplexZero_fst _ _ _ _ _ _) vL hvL z hz hK hcycL'
  -- ## Step 4: the fibre classes agree
  have hvL_lift : vL ≫ Work.SSSR.sSingP (Work.SSSR.StemsB.fibreIncl p
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
      = Work.SSSR.vertIncl p b s
        ≫ (SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)))
        ≫ Work.SSSR.liftFam p hfib (s+1) b σ h := by
    rw [hvL, hE]
  have hclass : (HomologicalComplex.homologyMap (Work.SSSR.sCCMap R vL) t)
        ((Work.SSSR.fibreCC p b).homologyπ t
          ((Work.SSSR.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))
      = (Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).homologyπ t
        ((Work.SSSR.fibreCC p (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).cyclesMk z'
          ((ComplexShape.down ℕ).next t) rfl hz') := by
    obtain ⟨γ, hγ⟩ := Work.SSSR.vertRestrTransportChains p hfib s t b σ h vL hvL_lift z hz hcycL'
    refine (Work.SSSR.pEZ_homologyπ_sCCMap_cyclesMk (Work.SSSR.sCCMap R vL) rfl z hz hcycL').symm.trans
      (hγ.symm.trans ?_)
    exact Work.SSSR.pEZ_transport_eq_of_triv p e₀ hfib hc t γ _ _ hm
  -- ## Step 5: both towers give the same class
  have key : (Work.SSSR.serreE1PieceIso p hfib s t (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).hom
        ((HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)) (s+t))
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
                (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplexZero p
                  (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s b σ h)).f (s+t)))
                (Work.SSSR.ezLinSnd s t
                  (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                  (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (Work.SSSR.stdIdSimplex s) z)))
            ((ComplexShape.down ℕ).next (s+t)) rfl hK))
      = (Work.SSSR.serreE1PieceIso p hfib s t (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).hom
        ((HomologicalComplex.homologyπ (Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)) (s+t))
          ((Work.SSSR.pieceAlong R (Work.SSSR.sSingP p)
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.pieceπOf (Work.SSSR.sSingP p)
                (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap R (Work.SSSR.ezSimplex p
                  (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib) s
                  (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
                  (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)).f (s+t)))
                (Work.SSSR.ezLinSnd s t
                  (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                  (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
                    (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
                  (Work.SSSR.stdIdSimplex s) z')))
            ((ComplexShape.down ℕ).next (s+t)) rfl hL)) := by
    rw [hL', hR]
    congr 1
    rw [Work.SSSR.pEZ_homologyπ_sCCMap_cyclesMk (Work.SSSR.sCCMap R vL) rfl z hz hcycL']
    rw [Work.SSSR.pEZ_homologyπ_sCCMap_cyclesMk
      (Work.SSSR.sCCMap R (𝟙 (Work.SSSR.sSing (Work.SSSR.StemsB.fibre p
        (Work.SSSR.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))))) rfl z' hz' hcycR']
    rw [Work.SSSR.pEZ_sCCMap_id, HomologicalComplex.homologyMap_id]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
    exact hclass
  exact Work.SSSR.pEZ_iso_hom_injective
    (Work.SSSR.serreE1PieceIso p hfib s t (SSet.stdSimplex.δ (n := s) 0 ≫ σ)) key

end Work.SSSR
