import Mathlib
import Submission.Work.Pi6.MSSK.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
variable (R : Type) [CommRing R] [Nontrivial R]

/-- The `Δ[s]`-component of a simplex of `T_σ = Δ[s] ×_{Sing B} Sing E`. -/
abbrev proj {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N⦌) :
    (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋N⦌ :=
  (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N⦌) w

/-- The `Sing E`-component of a simplex of `T_σ = Δ[s] ×_{Sing B} Sing E`. -/
abbrev comp {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N⦌) :
    (Work.SSSR.sSing E) _⦋N⦌ :=
  (pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋N⦌) w

/-- **The value of `thetaTop` on a generator** is `thetaVal`. -/
lemma genEval_thetaTop (p : C(E, B)) {s : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    Work.Cohomology.genEval R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) (thetaTop R p σ) w
      = thetaVal R p σ w := by
  have key : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w
      ≫ ModuleCat.ofHom (thetaTop R p σ)
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R R (thetaVal R p σ w)) := by
    rw [thetaTop]
    exact Cofan.IsColimit.fac _ _ _
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom (1:R)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h2
  rw [Work.Cohomology.genEval]
  exact h2.trans (by simp)

/-- **`IsTopFront`**: the monotone map underlying a simplex `α` of `Δ[s]` of dimension `N ≥ s`
is the identity on the first `s+1` vertices. -/
def IsTopFront {s N : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋N⦌) : Prop :=
  ∀ (h : s ≤ N), Work.Cohomology.frontIncl s N h ≫ SSet.stdSimplex.objEquiv α
    = 𝟙 (SimplexCategory.mk s)

/-- `thetaVal` is `1` exactly on the simplices over the top simplex. -/
lemma thetaVal_eq_one_iff {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (x : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s⦌) :
    thetaVal R p σ x = 1
      ↔ (pullback.fst σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk s)) x = topS s := by
  rw [thetaVal]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by norm_num) h

/-- The projection of a face of `T_σ` is the face of the projection. -/
lemma proj_δ {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N+1⦌) (i : Fin (N+2)) :
    (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N⦌)
        ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w)
      = (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).δ i
          ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N+1⦌) w) :=
  SSet.δ_naturality_apply (pullback.fst σ (Work.SSSR.sSingP p)) i w

/-- The `Sing E`-component of a face of `T_σ` is the face of the component. -/
lemma comp_δ {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N+1⦌) (i : Fin (N+2)) :
    (pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋N⦌)
        ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).δ i w)
      = (Work.SSSR.sSing E).δ i ((pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋N+1⦌) w) :=
  SSet.δ_naturality_apply (pullback.snd σ (Work.SSSR.sSingP p)) i w

/-- The projection of the front face. -/
lemma fst_frontFace {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (h : s ≤ N) (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N⦌) :
    (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s⦌)
        (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s N h w)
      = Work.Cohomology.frontFace
          (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s N h
            ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N⦌) w) :=
  NatTrans.naturality_apply (pullback.fst σ (Work.SSSR.sSingP p))
    (Work.Cohomology.frontIncl s N h).op w

/-- The projection of the back face. -/
lemma fst_backFace {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s + K⦌) :
    (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋K⦌)
        (Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s K w)
      = Work.Cohomology.backFace (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s K
          ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w) :=
  NatTrans.naturality_apply (pullback.fst σ (Work.SSSR.sSingP p)) (Work.Cohomology.backIncl s K).op w

/-- The `Sing E`-component of the back face. -/
lemma snd_backFace {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {K : ℕ} (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋s + K⦌) :
    (pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋K⦌)
        (Work.Cohomology.backFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s K w)
      = (Work.SSSR.sSing E).map (Work.Cohomology.backIncl s K).op
          ((pullback.snd σ (Work.SSSR.sSingP p)).app (op ⦋s+K⦌) w) :=
  NatTrans.naturality_apply (pullback.snd σ (Work.SSSR.sSingP p)) (Work.Cohomology.backIncl s K).op w

/-- The front face of a simplex of `Δ[s]` is the top simplex iff the underlying monotone map fixes
the first `s+1` vertices. -/
lemma frontFace_eq_topS_iff {s N : ℕ} (h : s ≤ N)
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋N⦌) :
    Work.Cohomology.frontFace (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s N h α
        = topS s
      ↔ Work.Cohomology.frontIncl s N h ≫ SSet.stdSimplex.objEquiv α = 𝟙 (SimplexCategory.mk s) := by
  show (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).map
      (Work.Cohomology.frontIncl s N h).op α = topS s ↔ _
  have hx : α = SSet.stdSimplex.objEquiv.symm
      (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk s) (m := op ⦋N⦌) α) :=
    (Equiv.symm_apply_apply _ _).symm
  rw [topS, hx, SSet.stdSimplex.map_objEquiv_symm]
  constructor
  · intro hh
    have h2 := congrArg (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk s) (m := op ⦋s⦌)) hh
    simpa using h2
  · intro hh
    have hh' : (Work.Cohomology.frontIncl s N h).op.unop ≫
        SSet.stdSimplex.objEquiv (n := SimplexCategory.mk s) (m := op ⦋N⦌) α
        = 𝟙 (unop (op ⦋s⦌)) := by simpa using hh
    rw [hh']

/-- The front face projection of a simplex of `T_σ` is the top simplex iff the simplex is
top-front. -/
lemma frontFace_fst_eq_topS_iff {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (h : s ≤ N) (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N⦌) :
    Work.Cohomology.frontFace
        (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) s N h
        ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N⦌) w) = topS s
      ↔ IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N⦌) w) := by
  rw [frontFace_eq_topS_iff]
  exact ⟨fun hh _ => hh, fun hh => hh h⟩

/-- **The value of `thetaTop` on the front face**: it is `1` iff the simplex is top-front. -/
lemma thetaVal_frontFace_eq_one_iff {s : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (h : s ≤ N) (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N⦌) :
    thetaVal R p σ
        (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) s N h w) = 1
      ↔ IsTopFront ((pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋N⦌) w) := by
  rw [thetaVal_eq_one_iff, fst_frontFace]
  exact frontFace_fst_eq_topS_iff p σ h w

/-- The value-level form of `IsTopFront`. -/
lemma isTopFront_val {s N : ℕ} {α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋N⦌}
    (hα : IsTopFront α) (h : s ≤ N) (i : Fin (N+1)) (hi : i.val ≤ s) :
    ((SSet.stdSimplex.objEquiv α).toOrderHom i).val = i.val := by
  have hmor : Work.Cohomology.frontIncl s N h ≫ SSet.stdSimplex.objEquiv α
      = 𝟙 (SimplexCategory.mk s) := hα h
  have h2 := congrArg (fun (f : ⦋s⦌ ⟶ ⦋s⦌) =>
    ((f.toOrderHom ⟨i.val, Nat.lt_succ_of_le hi⟩).val)) hmor
  simpa [Work.Cohomology.frontIncl] using h2

/-- The "tail" consequence of `IsTopFront`: all vertices beyond `s` map to the last vertex. -/
lemma isTopFront_tail {s N : ℕ} {α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) _⦋N⦌}
    (hα : IsTopFront α) (h : s ≤ N) (j : Fin (N+1)) (hj : s ≤ j.val) :
    (SSet.stdSimplex.objEquiv α).toOrderHom j = Fin.last s := by
  have hfix : (SSet.stdSimplex.objEquiv α).toOrderHom ⟨s, Nat.lt_succ_of_le h⟩ = Fin.last s := by
    have h0 := isTopFront_val hα h ⟨s, Nat.lt_succ_of_le h⟩ (le_refl s)
    exact Fin.ext h0
  have hmono := (SSet.stdSimplex.objEquiv α).toOrderHom.monotone
  have h1 : Fin.last s ≤ (SSet.stdSimplex.objEquiv α).toOrderHom j := by
    rw [← hfix]
    exact hmono (by simp only [Fin.le_def]; exact hj)
  have h2 : (SSet.stdSimplex.objEquiv α).toOrderHom j ≤ Fin.last s := Fin.le_last _
  exact le_antisymm h2 h1

/-- The last-face pasting map `T_{d_last σ} ⟶ T_σ`, spelled in the `pullAlong` normalisation. -/
noncomputable def lastFaceMapAlong {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {t : ℕ}
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.SSSR.pullAlong (Work.SSSR.sSingP p)
        (SSet.stdSimplex.δ (n := t) (Fin.last (t+1)) ≫ σ) ⟶
      Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ :=
  Work.SSSR.lastFaceMap (Work.SSSR.sSingP p) t σ

/-- The last-face analogue of `thetaVal`: the value on a `t`-simplex of `T_σ` is `1` iff its
projection is the top simplex of the last face of `Δ[t+1]`. -/
def lastFaceVal {t : ℕ} (R : Type) [CommRing R] (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t⦌) : R := by
  classical
  exact if (pullback.fst σ (Work.SSSR.sSingP p)).app (op (SimplexCategory.mk t)) w
      = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1)))
    then 1 else 0

/-- **The top cochain of the last face**, pulled back to `T_σ`: the indicator cochain of the
simplices of `T_σ` lying over the top simplex of the last face. -/
def lastFaceTop (R : Type) [CommRing R] {t : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B) :
    Work.Cohomology.Cochain R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t :=
  ((Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).isColimitChainComplexXCofan (ModuleCat.of R R) t).desc
    (Cofan.mk (ModuleCat.of R R) (fun w =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R (lastFaceVal R p σ w)))) |>.hom

/-- The value of `lastFaceTop` on a generator. -/
lemma genEval_lastFaceTop {t : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋t⦌) :
    Work.Cohomology.genEval R (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ)
        (lastFaceTop R p σ) w = lastFaceVal R p σ w := by
  have key : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ).ιChainComplex (R := ModuleCat.of R R) w
      ≫ ModuleCat.ofHom (lastFaceTop R p σ)
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R R (lastFaceVal R p σ w)) := by
    rw [lastFaceTop]
    exact Cofan.IsColimit.fac _ _ _
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom (1:R)) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h2
  rw [Work.Cohomology.genEval]
  exact h2.trans (by simp)

/-- The front face of a `t`-simplex of `T_σ` is over the top simplex of the last face iff the
projection is the top simplex of the last face. -/
lemma lastFaceVal_frontFace_eq_one_iff {t : ℕ} (p : C(E, B))
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (t+1)) : SSet.{0}) ⟶ Work.SSSR.sSing B)
    {N : ℕ} (h : t ≤ N) (w : (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) _⦋N⦌) :
    lastFaceVal R p σ (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t N h w)
        = 1
      ↔ (pullback.fst σ (Work.SSSR.sSingP p)).app (op ⦋t⦌)
          (Work.Cohomology.frontFace (Work.SSSR.pullAlong (Work.SSSR.sSingP p) σ) t N h w)
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ (Fin.last (t+1))) := by
  rw [lastFaceVal]
  split_ifs with hh
  · exact iff_of_true rfl hh
  · exact iff_of_false (by norm_num) hh


end

end Work.Pi6.MSSK
