import Mathlib
import Submission.Work.SSS.serreE1D1
import Submission.Work.SSS.serreE1EZ
import Submission.Work.SSS.serreE1PieceExplicit
import Submission.Work.SSS.serreE1PieceIotaDefs
import Submission.Work.SSS.serreE1Assembly
import Submission.Work.SSS.ezGen_snd_sum_zero
import Submission.Work.SSS.piszDefs
import Submission.Work.SSS.iotaF_chainMap
import Submission.Work.SSS.ezLinSnd_map_fst
import Submission.Work.SSS.sSing_fibre_factor
import Submission.Work.SSS.sigmaVert_app_ssetVertex
import Submission.Work.SSS.pieceIso_lift_chain
import Submission.Work.SSS.vertRestrTransportChains

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 800000

/-- **The defining property of the trivialisation `Work.SSS.triv`.**  For every path `γ : b → b'`,
the canonical fibre transport along `γ` followed by `triv b'` is `triv b`. -/
lemma triv_transport {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) {b b' : B} (γ : Path b b') :
    Work.SSS.transportIsoPath p hfib γ t ≪≫ Work.SSS.triv p e₀ hfib hc t b'
      = Work.SSS.triv p e₀ hfib hc t b :=
  (Classical.choose_spec (Work.SSS.fibreTrivializationOfSimplyConn p (p e₀) t
    (fun {b b'} γ => Work.SSS.transportIsoPath p hfib γ t)
    (fun γ δ => Work.SSS.transportIsoPath_trans p hfib t γ δ)
    (fun γ γ' H => Work.SSS.transportIsoPath_homotopic p hfib t γ γ' H) hc)) γ


/-! ## Elementary homology lemmas (local copies of the ones in
`Submission/Work/SSS/pieceIso_ezSimplexZero.lean`, which cannot be imported here: that module
depends on the still-`sorry`ed `Work.SSS.vertRestr_transport`.) -/

/-- The differential of the induced chain map, elementwise. -/
lemma pEZ_sCCMap_d_applyA {X Y : SSet.{0}} (g : X ⟶ Y) (i j : ℕ) (x : (sCC X).X i) :
    (sCC Y).d i j ((sCCMap g).f i x) = (sCCMap g).f j ((sCC X).d i j x) := by
  have h := congrArg (fun (g : (sCC X).X i ⟶ (sCC Y).X j) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm (sCCMap g) i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- `homologyπ` is natural with respect to `homologyMap`. -/
lemma pEZ_homologyπ_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (x : K.cycles i) :
    (L.homologyπ i) ((HomologicalComplex.cyclesMap φ i) x)
      = (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) x) :=
  (congrArg (fun (f : K.cycles i ⟶ L.homology i) => f x)
    (HomologicalComplex.homologyπ_naturality φ i)).symm

/-- The `iCycles` inclusion of a `cyclesMk`. -/
lemma pEZ_iCycles_cyclesMk {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : ((forget₂ (ModuleCat ℤ) Ab).map (K.d i j)) x = 0) :
    (ConcreteCategory.hom (K.iCycles i)) (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

/-- `cyclesMap` on a `cyclesMk`. -/
lemma pEZ_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
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
lemma pEZ_homologyπ_sCCMap_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : (ModuleCat.Hom.hom (K.d i j)) x = 0)
    (hx' : (ModuleCat.Hom.hom (L.d i j)) ((φ.f i) x) = 0) :
    (L.homologyπ i) (L.cyclesMk ((φ.f i) x) j hj hx')
      = (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) (K.cyclesMk x j hj hx)) := by
  rw [← pEZ_cyclesMap_cyclesMk φ hj x hx hx']
  exact pEZ_homologyπ_map φ i (K.cyclesMk x j hj hx)

/-- An isomorphism of modules is injective on elements. -/
lemma pEZ_iso_hom_injective {A B : ModuleCat ℤ} (e : A ≅ B) : Function.Injective e.hom := by
  intro a b hab
  have h := congrArg (fun z => e.inv.hom z) hab
  simpa only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id,
    LinearMap.id_apply] using h

/-- The chain map induced by the identity is the identity. -/
lemma pEZ_sCCMap_id (X : SSet.{0}) : sCCMap (𝟙 X) = 𝟙 (sCC X) := by
  simp [sCCMap]

/-- **Transport comparison of `triv`-equivalent fibre classes.**  If two fibre homology classes
have the same image under the trivialisation `triv`, they correspond under the canonical transport
along any path between the base points. -/
lemma pEZ_transport_eq_of_triv {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (t : ℕ) {b b' : B} (γ : Path b b')
    (z : Work.PiS.HZ (Work.StemsB.fibre p b) t)
    (z' : Work.PiS.HZ (Work.StemsB.fibre p b') t)
    (hm : (Work.SSS.triv p e₀ hfib hc t b').hom z'
      = (Work.SSS.triv p e₀ hfib hc t b).hom z) :
    (Work.SSS.transportIsoPath p hfib γ t).hom z = z' := by
  have hnat : (Work.SSS.triv p e₀ hfib hc t b').hom
      ((Work.SSS.transportIsoPath p hfib γ t).hom z)
      = (Work.SSS.triv p e₀ hfib hc t b).hom z := by
    have h := triv_transport p e₀ hfib hc t γ
    exact congrArg (fun (e : Work.PiS.HZ (Work.StemsB.fibre p b) t ≅ Work.SSS.coefM p e₀ t)
      => e.hom z) h
  exact pEZ_iso_hom_injective (Work.SSS.triv p e₀ hfib hc t b') (by rw [hnat, ← hm])

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
non-vacuous) form of `Work.SSS.pieceIso_ezSimplexZero`: for a simplex of even degree `≥ 2` the
hypothesis `∂τ = 0` is unsatisfiable, so the simplex-level statement says nothing in those
degrees.  Equivalently (`(ε_{δ 0 ≫ σ})` being an isomorphism) the iterated last-face connecting
map sends `[K]` to `c s` times the `triv`-transport of `[z]`.

Route.  `cases s`; for `s = 0` the statement is that the `v₁`-vertex restriction `vres` of the
coherent lift `liftFam p hfib 1 b (σ)` (the base point of `δ 0 ≫ σ` is `σ(v₁)`, and
`Δ[0] ⊗ F_b ≅ F_b`) induces the same map on homology as the canonical transport
`transportIsoPath p hfib γ`, i.e. `Work.SSS.transport_eq_topEnd` combined with
`Work.SSS.fibreTrivializationOfSimplyConn`'s defining property of `triv`; for `s+1` peel the last
face exactly as in the proof of `Work.SSS.serreE1PieceIso_iota_step`
(`Work.SSS.iotaTBdryHorn`, `Work.SSS.pieceBdryHornIsoIso`) — the only new ingredient is that the
`i = 0` face keeps `ezSimplexZero`, for which the base case applies after transporting.
The helpers `hK`, `hL` (that the two chains are cycles in the piece) follow from the linearised
Eilenberg–Zilber boundary formula `Work.SSS.ezLinSnd_boundary` and `hz`, `hz'`; the prover should
add them as local lemmas of the same file if useful. -/
theorem ezSimplexZero_chain_class {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hc : Work.PiS.SimplyConn B (p e₀)) (s t : ℕ) (b : B)
    (σ : ((SSet.stdSimplex.obj (SimplexCategory.mk (s+1)) : SSet.{0})) ⟶ Work.SSS.sSing B)
    (h : Work.SSS.sigmaVert σ = b)
    (z : (Work.SSS.fibreCC p b).X t)
    (hz : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p b).d t ((ComplexShape.down ℕ).next t))) z = 0)
    (z' : (Work.SSS.fibreCC p (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).X t)
    (hz' : (ModuleCat.Hom.hom ((Work.SSS.fibreCC p
              (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).d t
              ((ComplexShape.down ℕ).next t))) z' = 0)
    (hK : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).d (s+t) ((ComplexShape.down ℕ).next (s+t))))
          ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplexZero p
              (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b σ h)).f (s+t)))
              (Work.SSS.ezLinSnd s t
                (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex s) z))) = 0)
    (hL : (ModuleCat.Hom.hom ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).d (s+t) ((ComplexShape.down ℕ).next (s+t))))
          ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p
              (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
              (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)).f (s+t)))
              (Work.SSS.ezLinSnd s t
                (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p
                  (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
                (Work.SSS.stdIdSimplex s) z'))) = 0)
    (hm : (ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t
            (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).hom)
          ((Work.SSS.fibreCC p
              (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).homologyπ t
            ((Work.SSS.fibreCC p
                (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).cyclesMk z'
              ((ComplexShape.down ℕ).next t) rfl hz'))
        = (ModuleCat.Hom.hom (Work.SSS.triv p e₀ hfib hc t b).hom)
            ((Work.SSS.fibreCC p b).homologyπ t
              ((Work.SSS.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))) :
    (Work.SSS.pieceAlong (Work.SSS.sSingP p)
        (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).homologyπ (s+t)
        ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
          ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
            ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplexZero p
              (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b σ h)).f (s+t)))
              (Work.SSS.ezLinSnd s t
                (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex s) z)))
          ((ComplexShape.down ℕ).next (s+t)) rfl hK)
      = (Work.SSS.pieceAlong (Work.SSS.sSingP p)
          (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).homologyπ (s+t)
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p
                (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
                (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
                (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)).f (s+t)))
                (Work.SSS.ezLinSnd s t
                  (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p
                    (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
                  (Work.SSS.stdIdSimplex s) z')))
            ((ComplexShape.down ℕ).next (s+t)) rfl hL) := by
  -- ## Step 1: the vertex-`1` restriction `vL` of the `0`-face lift
  have hE : Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b σ h
      ≫ pullback.snd (SSet.stdSimplex.δ (n := s) 0 ≫ σ) (Work.SSS.sSingP p)
      = (SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
        ≫ Work.SSS.liftFam p hfib (s+1) b σ h := by
    rw [Work.SSS.ezSimplexZero_snd, Category.assoc, Work.SSS.ezSimplex_snd]
  have hLP : ((SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
        ≫ Work.SSS.liftFam p hfib (s+1) b σ h) ≫ Work.SSS.sSingP p
      = SemiCartesianMonoidalCategory.fst (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
          (Work.SSS.sSing (Work.StemsB.fibre p b)) ≫ (SSet.stdSimplex.δ (n := s) 0 ≫ σ) := by
    rw [Category.assoc, Work.SSS.liftFam_proj, ← Category.assoc,
      CartesianMonoidalCategory.tensorHom_fst, Category.assoc]
  have hwconst : (Work.SSS.vertIncl p b s
        ≫ Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b σ h
        ≫ pullback.snd (SSet.stdSimplex.δ (n := s) 0 ≫ σ) (Work.SSS.sSingP p))
        ≫ Work.SSS.sSingP p
      = SSet.const (TopCat.toSSetObj₀Equiv.symm
          (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))) := by
    rw [hE]
    rw [Category.assoc]
    rw [hLP]
    rw [← Category.assoc]
    rw [Work.SSS.vertIncl_fst]
    rw [SSet.const_comp]
    congr 1
    rw [Equiv.eq_symm_apply]
    exact Work.SSS.sigmaVert_app_ssetVertex (SSet.stdSimplex.δ (n := s) 0 ≫ σ)
  obtain ⟨vL, hvL⟩ := Work.SSS.sSing_fibre_factor p
      (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
      (Work.SSS.sSing (Work.StemsB.fibre p b))
      (Work.SSS.vertIncl p b s ≫ Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib)
        (Work.SSS.liftFam_proj p hfib) s b σ h
        ≫ pullback.snd (SSet.stdSimplex.δ (n := s) 0 ≫ σ) (Work.SSS.sSingP p)) hwconst
  -- ## Step 2: the cycle conditions of the two towers
  have hcycR' : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))).d t
      ((ComplexShape.down ℕ).next t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (𝟙 (Work.SSS.sSing (Work.StemsB.fibre p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))))).f t)) (z')) = 0 := by
    simpa using hz'
  have hcycL' : (ModuleCat.Hom.hom ((Work.SSS.sCC (Work.SSS.sSing (Work.StemsB.fibre p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))).d t
      ((ComplexShape.down ℕ).next t)))
      ((ModuleCat.Hom.hom ((Work.SSS.sCCMap vL).f t)) (z)) = 0 := by
    rw [Work.SSS.pEZ_sCCMap_d_applyA vL t ((ComplexShape.down ℕ).next t) z, hz]
    simp
  -- ## Step 3: the two tower comparisons
  have hR := Work.SSS.pieceIso_lift_chain p hfib Work.SSS.ezccSign Work.SSS.ezccSign_zero
      Work.SSS.ezccSign_succ s t (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
      (SSet.stdSimplex.δ (n := s) 0 ≫ σ)
      (Work.SSS.ezSimplex p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
        (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)
      (Work.SSS.ezSimplex_fst _ _ _ _ _ _)
      (𝟙 (Work.SSS.sSing (Work.StemsB.fibre p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))))
      (by rw [Category.id_comp, Work.SSS.ezSimplex_snd, Work.SSS.liftFam_vert])
      z' hz' hL hcycR'
  have hL' := Work.SSS.pieceIso_lift_chain p hfib Work.SSS.ezccSign Work.SSS.ezccSign_zero
      Work.SSS.ezccSign_succ s t b (SSet.stdSimplex.δ (n := s) 0 ≫ σ)
      (Work.SSS.ezSimplexZero p (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b σ h)
      (Work.SSS.ezSimplexZero_fst _ _ _ _ _ _) vL hvL z hz hK hcycL'
  -- ## Step 4: the fibre classes agree
  have hvL_lift : vL ≫ Work.SSS.sSingP (Work.StemsB.fibreIncl p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))
      = Work.SSS.vertIncl p b s
        ≫ (SSet.stdSimplex.δ (n := s) 0 ⊗ₘ 𝟙 (Work.SSS.sSing (Work.StemsB.fibre p b)))
        ≫ Work.SSS.liftFam p hfib (s+1) b σ h := by
    rw [hvL, hE]
  have hclass : (HomologicalComplex.homologyMap (Work.SSS.sCCMap vL) t)
        ((Work.SSS.fibreCC p b).homologyπ t
          ((Work.SSS.fibreCC p b).cyclesMk z ((ComplexShape.down ℕ).next t) rfl hz))
      = (Work.SSS.fibreCC p (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).homologyπ t
        ((Work.SSS.fibreCC p (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))).cyclesMk z'
          ((ComplexShape.down ℕ).next t) rfl hz') := by
    obtain ⟨γ, hγ⟩ := Work.SSS.vertRestrTransportChains p hfib s t b σ h vL hvL_lift z hz hcycL'
    refine (Work.SSS.pEZ_homologyπ_sCCMap_cyclesMk (Work.SSS.sCCMap vL) rfl z hz hcycL').symm.trans
      (hγ.symm.trans ?_)
    exact Work.SSS.pEZ_transport_eq_of_triv p e₀ hfib hc t γ _ _ hm
  -- ## Step 5: both towers give the same class
  have key : (Work.SSS.serreE1PieceIso p hfib s t (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).hom
        ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)) (s+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
                (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplexZero p
                  (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s b σ h)).f (s+t)))
                (Work.SSS.ezLinSnd s t
                  (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p b)) (Work.SSS.stdIdSimplex s) z)))
            ((ComplexShape.down ℕ).next (s+t)) rfl hK))
      = (Work.SSS.serreE1PieceIso p hfib s t (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).hom
        ((HomologicalComplex.homologyπ (Work.SSS.pieceAlong (Work.SSS.sSingP p)
            (SSet.stdSimplex.δ (n := s) 0 ≫ σ)) (s+t))
          ((Work.SSS.pieceAlong (Work.SSS.sSingP p)
              (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSS.pieceπOf (Work.SSS.sSingP p)
                (SSet.stdSimplex.δ (n := s) 0 ≫ σ)).f (s+t)))
              ((ModuleCat.Hom.hom ((Work.SSS.sCCMap (Work.SSS.ezSimplex p
                  (Work.SSS.liftFam p hfib) (Work.SSS.liftFam_proj p hfib) s
                  (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))
                  (SSet.stdSimplex.δ (n := s) 0 ≫ σ) rfl)).f (s+t)))
                (Work.SSS.ezLinSnd s t
                  (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0})
                  (Work.SSS.sSing (Work.StemsB.fibre p
                    (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ))))
                  (Work.SSS.stdIdSimplex s) z')))
            ((ComplexShape.down ℕ).next (s+t)) rfl hL)) := by
    rw [hL', hR]
    congr 1
    rw [Work.SSS.pEZ_homologyπ_sCCMap_cyclesMk (Work.SSS.sCCMap vL) rfl z hz hcycL']
    rw [Work.SSS.pEZ_homologyπ_sCCMap_cyclesMk
      (Work.SSS.sCCMap (𝟙 (Work.SSS.sSing (Work.StemsB.fibre p
        (Work.SSS.sigmaVert (SSet.stdSimplex.δ (n := s) 0 ≫ σ)))))) rfl z' hz' hcycR']
    rw [Work.SSS.pEZ_sCCMap_id, HomologicalComplex.homologyMap_id]
    simp only [ModuleCat.hom_id, LinearMap.id_apply]
    exact hclass
  exact Work.SSS.pEZ_iso_hom_injective
    (Work.SSS.serreE1PieceIso p hfib s t (SSet.stdSimplex.δ (n := s) 0 ≫ σ)) key

end Work.SSS
