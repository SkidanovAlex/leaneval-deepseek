import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.BallKFrame` — the space `D_V/S_V` and its function algebra

Infrastructure for `Work.KT.ball_K`.  The pair `(D_V, S_V)` is realised as a genuine compact
Hausdorff space `Xq V` (the range of the map `z ↦ (‖z‖, (1-‖z‖)•z)` into `ℝ × V`), so that the
Bott product theorem `Work.KT.fund_product` can be applied to it.
-/

namespace Work.KT

open Matrix

noncomputable section

section Basic

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The map `D_V → ℝ × V` whose range models `D_V/S_V`: it collapses the boundary to one point
and is injective on the interior. -/
def suspFun : Ball V → ℝ × V := fun z => (‖(z : V)‖, (1 - ‖(z : V)‖) • (z : V))

/-- The model of `D_V/S_V`: the range of `suspFun`, a compact Hausdorff space. -/
abbrev Xq : Type := Set.range (suspFun V)

lemma continuous_suspFun : Continuous (suspFun V) := by
  unfold suspFun; fun_prop

/-- The model of the quotient map `D_V → D_V/S_V`. -/
def qMap : C(Ball V, Xq V) :=
  ⟨fun z => ⟨suspFun V z, z, rfl⟩, (continuous_suspFun V).subtype_mk _⟩

@[simp]
lemma qMap_apply (z : Ball V) : qMap V z = ⟨suspFun V z, z, rfl⟩ := rfl

lemma suspFun_eq_iff {z z' : Ball V} :
    suspFun V z = suspFun V z' ↔ z = z' ∨ (z ∈ bdry V ∧ z' ∈ bdry V) := by
  constructor
  · intro h
    have h1 : ‖(z : V)‖ = ‖(z' : V)‖ := congrArg Prod.fst h
    have h2 : (1 - ‖(z : V)‖) • (z : V) = (1 - ‖(z' : V)‖) • (z' : V) :=
      congrArg Prod.snd h
    by_cases hz : ‖(z : V)‖ = 1
    · right
      refine ⟨by simpa [bdry] using hz, ?_⟩
      simp only [bdry, Set.mem_ofPred_eq]
      rw [← h1]; exact hz
    · left
      have h3 : (1 - ‖(z : V)‖) • (z : V) = (1 - ‖(z : V)‖) • (z' : V) := by
        rw [h2, h1]
      have h4 : (1 : ℝ) - ‖(z : V)‖ ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
      exact Subtype.ext (smul_right_injective V h4 h3)
  · rintro (rfl | ⟨hz, hz'⟩)
    · rfl
    · have h1 : ‖(z : V)‖ = 1 := hz
      have h2 : ‖(z' : V)‖ = 1 := hz'
      simp [suspFun, h1, h2]

lemma qMap_eq_iff {z z' : Ball V} :
    qMap V z = qMap V z' ↔ z = z' ∨ (z ∈ bdry V ∧ z' ∈ bdry V) := by
  rw [← suspFun_eq_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

lemma eq_of_qMap_eq_of_notMem {z z' : Ball V} (h : qMap V z = qMap V z')
    (hz : z ∉ bdry V) : z = z' := by
  rcases (qMap_eq_iff V).mp h with h' | ⟨h1, _⟩
  · exact h'
  · exact absurd h1 hz

end Basic

section Topology

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

instance instCompactSpaceBall [ProperSpace V] : CompactSpace (Ball V) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V) 1)

instance instCompactSpaceXq [ProperSpace V] : CompactSpace (Xq V) :=
  isCompact_iff_compactSpace.mp (isCompact_range (continuous_suspFun V))

instance instNonemptyXq : Nonempty (Xq V) :=
  ⟨qMap V 0⟩

lemma surjective_qMap : Function.Surjective (qMap V) := by
  rintro ⟨y, z, rfl⟩
  exact ⟨z, rfl⟩

lemma isQuotientMap_qMap [ProperSpace V] : Topology.IsQuotientMap (qMap V) :=
  Topology.IsQuotientMap.of_surjective_continuous (surjective_qMap V) (qMap V).continuous

end Topology

section Iso

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]

/-- Two boundary points give the same point of `Xq V`. -/
lemma qMap_eq_of_mem_bdry {z z' : Ball V} (hz : z ∈ bdry V) (hz' : z' ∈ bdry V) :
    qMap V z = qMap V z' :=
  (qMap_eq_iff V).mpr (Or.inr ⟨hz, hz'⟩)

/-- Pull-back of a function on `Xq V`: this is an element of `Kpair V`. -/
def qPullFun (g : C(Xq V, ℂ)) : Kpair V :=
  ⟨(pullAlg (qMap V)) g, by
    intro x hx y hy
    simp only [pullAlg, AlgHom.comp_apply, StarAlgHom.coe_toAlgHom,
      ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_apply]
    rw [qMap_eq_of_mem_bdry V hx hy]⟩

@[simp]
lemma qPullFun_coe (g : C(Xq V, ℂ)) :
    ((qPullFun V g : Kpair V) : C(Ball V, ℂ)) = (pullAlg (qMap V)) g := rfl

/-- `C(Xq V, ℂ) → Kpair V` by pull-back along the quotient map. -/
def qPull : C(Xq V, ℂ) →ₐ[ℂ] Kpair V where
  toFun := qPullFun V
  map_one' := by ext z; simp [qPullFun]
  map_mul' := by intro f g; ext z; simp [qPullFun]
  map_zero' := by ext z; simp [qPullFun]
  map_add' := by intro f g; ext z; simp [qPullFun]
  commutes' := by intro c; ext z; simp [qPullFun]

/-- `Kpair V → C(Xq V, ℂ)`: descend a function constant on the boundary along the quotient map. -/
def qPush : Kpair V →ₐ[ℂ] C(Xq V, ℂ) where
  toFun h := (isQuotientMap_qMap V).lift ((Kpair V).val h) (by
    intro z z' hzz'
    rcases (qMap_eq_iff V).mp hzz' with h | ⟨hz, hz'⟩
    · rw [h]
    · exact h.2 z hz z' hz')
  map_one' := by
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMap V x
    simp [Topology.IsQuotientMap.lift_comp]
  map_mul' := by
    intro f g
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMap V x
    simp [Topology.IsQuotientMap.lift_comp]
  map_zero' := by
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMap V x
    simp [Topology.IsQuotientMap.lift_comp]
  map_add' := by
    intro f g
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMap V x
    simp [Topology.IsQuotientMap.lift_comp]
  commutes' := by
    intro c
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMap V x
    simp [Topology.IsQuotientMap.lift_comp]

lemma qPush_comp_qMap (h : Kpair V) :
    (qPush V h).comp (qMap V) = (Kpair V).val h :=
  Topology.IsQuotientMap.lift_comp _ _ _

lemma qPull_qPush (h : Kpair V) : qPull V (qPush V h) = h := by
  apply Subtype.ext
  show ((qPull V (qPush V h) : Kpair V) : C(Ball V, ℂ)) = ((Kpair V).val h : C(Ball V, ℂ))
  rw [show ((qPull V (qPush V h) : Kpair V) : C(Ball V, ℂ)) = (qPush V h).comp (qMap V) from rfl]
  exact qPush_comp_qMap V h

lemma qPush_qPull (g : C(Xq V, ℂ)) : qPush V (qPull V g) = g := by
  ext x
  obtain ⟨z, rfl⟩ := surjective_qMap V x
  show (qPush V (qPull V g)) (qMap V z) = g (qMap V z)
  rw [← ContinuousMap.comp_apply, qPush_comp_qMap V (qPull V g)]
  rfl

/-- `Kpair V` and `C(Xq V, ℂ)` are the same algebra. -/
def qIso : Kpair V ≃ₐ[ℂ] C(Xq V, ℂ) where
  toFun := qPush V
  invFun := qPull V
  left_inv := qPull_qPush V
  right_inv := qPush_qPull V
  map_mul' := (qPush V).map_mul'
  map_add' := (qPush V).map_add'
  commutes' := (qPush V).commutes'

end Iso

end

end Work.KT

namespace Work.KT

open Matrix

noncomputable section

section Prod

variable (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]

/-- `D_{V×W} → Xq V × Xq W` (the product of the two quotient maps). -/
def qMapProd : C(Ball (V × W), Xq V × Xq W) :=
  ⟨fun z => (qMap V (prFst V W z), qMap W (prSnd V W z)),
    ((qMap V).continuous.comp (prFst V W).continuous).prodMk
      ((qMap W).continuous.comp (prSnd V W).continuous)⟩

@[simp]
lemma qMapProd_apply (z : Ball (V × W)) :
    qMapProd V W z = (qMap V (prFst V W z), qMap W (prSnd V W z)) := rfl

/-- The fibre relation of `qMapProd` is exactly the defining relation of `prodAlg V W`. -/
lemma qMapProd_eq_iff {z z' : Ball (V × W)} :
    qMapProd V W z = qMapProd V W z' ↔
      (((z : V × W).1 = (z' : V × W).1 ∨
          (‖(z : V × W).1‖ = 1 ∧ ‖(z' : V × W).1‖ = 1)) ∧
        ((z : V × W).2 = (z' : V × W).2 ∨
          (‖(z : V × W).2‖ = 1 ∧ ‖(z' : V × W).2‖ = 1))) := by
  have key1 : ∀ (a a' : Ball V), qMap V a = qMap V a' ↔
      ((a : V) = (a' : V) ∨ (‖(a : V)‖ = 1 ∧ ‖(a' : V)‖ = 1)) := by
    intro a a'; rw [qMap_eq_iff]; simp only [bdry, Set.mem_ofPred_eq, Subtype.ext_iff]
  have key2 : ∀ (b b' : Ball W), qMap W b = qMap W b' ↔
      ((b : W) = (b' : W) ∨ (‖(b : W)‖ = 1 ∧ ‖(b' : W)‖ = 1)) := by
    intro b b'; rw [qMap_eq_iff]; simp only [bdry, Set.mem_ofPred_eq, Subtype.ext_iff]
  simp only [qMapProd_apply, Prod.mk.injEq]
  exact and_congr (key1 (prFst V W z) (prFst V W z')) (key2 (prSnd V W z) (prSnd V W z'))

/-- Membership in `prodAlg` is exactly constancy on the fibres of `qMapProd`. -/
lemma mem_prodAlg_iff (F : C(Ball (V × W), ℂ)) :
    F ∈ prodAlg V W ↔ ∀ z z' : Ball (V × W), qMapProd V W z = qMapProd V W z' → F z = F z' := by
  constructor
  · intro hF z z' hz
    obtain ⟨hF1, hF2⟩ := hF
    rcases (qMapProd_eq_iff V W).mp hz with ⟨h1, h2⟩
    rcases h1 with h1 | ⟨h1, h1'⟩
    · rcases h2 with h2 | ⟨h2, h2'⟩
      · rw [Subtype.ext (Prod.ext h1 h2)]
      · exact hF2 z z' h2 h2' h1
    · rcases h2 with h2 | ⟨h2, h2'⟩
      · exact hF1 z z' h1 h1' h2
      · have hz1 : ‖(z : V × W).1‖ ≤ 1 := by
          have h := Metric.mem_closedBall.mp z.2
          rw [dist_zero_right, Prod.norm_def] at h
          exact (le_max_left _ _).trans h
        have hz2 : ‖(z' : V × W).2‖ ≤ 1 := by
          have h := Metric.mem_closedBall.mp z'.2
          rw [dist_zero_right, Prod.norm_def] at h
          exact (le_max_right _ _).trans h
        have hmem : ((z : V × W).1, (z' : V × W).2) ∈ Metric.closedBall (0 : V × W) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
          exact max_le hz1 hz2
        have hF2' := hF2 z ⟨((z : V × W).1, (z' : V × W).2), hmem⟩ h2 h2' rfl
        rw [hF2']
        exact hF1 _ z' h1 h1' rfl
  · intro hF
    refine ⟨?_, ?_⟩
    · intro z z' h1 h1' h2
      exact hF z z' ((qMapProd_eq_iff V W).mpr ⟨Or.inr ⟨h1, h1'⟩, Or.inl h2⟩)
    · intro z z' h1 h1' h2
      exact hF z z' ((qMapProd_eq_iff V W).mpr ⟨Or.inl h2, Or.inr ⟨h1, h1'⟩⟩)

end Prod

end

end Work.KT

namespace Work.KT

open Matrix

noncomputable section

section ProdIso

variable (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]

instance instCompactSpaceProdBall : CompactSpace (Ball (V × W)) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V × W) 1)

lemma surjective_qMapProd : Function.Surjective (qMapProd V W) := by
  rintro ⟨x, y⟩
  obtain ⟨z, hz⟩ := x.2
  obtain ⟨z', hz'⟩ := y.2
  have hx : x = ⟨suspFun V z, z, rfl⟩ := Subtype.ext hz.symm
  have hy : y = ⟨suspFun W z', z', rfl⟩ := Subtype.ext hz'.symm
  refine ⟨⟨(z, z'), ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    have h1 := (Metric.mem_closedBall.mp z.2 : dist (z : V) 0 ≤ 1)
    have h2 := (Metric.mem_closedBall.mp z'.2 : dist (z' : W) 0 ≤ 1)
    rw [dist_zero_right] at h1 h2
    exact max_le h1 h2
  · rw [hx, hy]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show suspFun V (prFst V W ⟨(z, z'), _⟩) = suspFun V z
      rfl
    · show suspFun W (prSnd V W ⟨(z, z'), _⟩) = suspFun W z'
      rfl

lemma isQuotientMap_qMapProd : Topology.IsQuotientMap (qMapProd V W) :=
  Topology.IsQuotientMap.of_surjective_continuous (surjective_qMapProd V W)
    (qMapProd V W).continuous

/-- Pull-back of a function on `Xq V × Xq W` is an element of `prodAlg V W`. -/
def prodPullFun (g : C(Xq V × Xq W, ℂ)) : prodAlg V W :=
  ⟨(pullAlg (qMapProd V W)) g, by
    rw [mem_prodAlg_iff]
    intro z z' hz
    simp only [pullAlg, AlgHom.coe_mk, StarAlgHom.coe_toAlgHom, MonoidWithZeroHom.coe_mk,
      ZeroHom.coe_mk, ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_apply]
    rw [hz]⟩

@[simp]
lemma prodPullFun_coe (g : C(Xq V × Xq W, ℂ)) :
    ((prodPullFun V W g : prodAlg V W) : C(Ball (V × W), ℂ)) = (pullAlg (qMapProd V W)) g :=
  rfl

/-- `C(Xq V × Xq W, ℂ) → prodAlg V W` by pull-back. -/
def prodPull : C(Xq V × Xq W, ℂ) →ₐ[ℂ] prodAlg V W where
  toFun := prodPullFun V W
  map_one' := by ext z; simp [prodPullFun]
  map_mul' := by intro f g; ext z; simp [prodPullFun]
  map_zero' := by ext z; simp [prodPullFun]
  map_add' := by intro f g; ext z; simp [prodPullFun]
  commutes' := by intro c; ext z; simp [prodPullFun]

/-- `prodAlg V W → C(Xq V × Xq W, ℂ)`: descend along the product quotient map. -/
def prodPush : prodAlg V W →ₐ[ℂ] C(Xq V × Xq W, ℂ) where
  toFun F := (isQuotientMap_qMapProd V W).lift ((prodAlg V W).val F) (by
    intro z z' hzz'
    exact (mem_prodAlg_iff V W F).mp F.2 z z' hzz')
  map_one' := by
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
    simp [Topology.IsQuotientMap.lift_comp]
  map_mul' := by
    intro f g
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
    simp [Topology.IsQuotientMap.lift_comp]
  map_zero' := by
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
    simp [Topology.IsQuotientMap.lift_comp]
  map_add' := by
    intro f g
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
    simp [Topology.IsQuotientMap.lift_comp]
  commutes' := by
    intro c
    ext x
    obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
    simp [Topology.IsQuotientMap.lift_comp]

lemma prodPush_comp_qMapProd (F : prodAlg V W) :
    (prodPush V W F).comp (qMapProd V W) = (prodAlg V W).val F :=
  Topology.IsQuotientMap.lift_comp _ _ _

lemma prodPull_prodPush (F : prodAlg V W) : prodPull V W (prodPush V W F) = F := by
  apply Subtype.ext
  show ((prodPull V W (prodPush V W F) : prodAlg V W) : C(Ball (V × W), ℂ)) =
    ((prodAlg V W).val F : C(Ball (V × W), ℂ))
  rw [show ((prodPull V W (prodPush V W F) : prodAlg V W) : C(Ball (V × W), ℂ)) =
    (prodPush V W F).comp (qMapProd V W) from rfl]
  exact prodPush_comp_qMapProd V W F

lemma prodPush_prodPull (g : C(Xq V × Xq W, ℂ)) : prodPush V W (prodPull V W g) = g := by
  ext x
  obtain ⟨z, rfl⟩ := surjective_qMapProd V W x
  show (prodPush V W (prodPull V W g)) (qMapProd V W z) = g (qMapProd V W z)
  rw [← ContinuousMap.comp_apply, prodPush_comp_qMapProd V W (prodPull V W g)]
  rfl

/-- `prodAlg V W` is the function algebra of `Xq V × Xq W`. -/
def prodIso : prodAlg V W ≃ₐ[ℂ] C(Xq V × Xq W, ℂ) where
  toFun := prodPush V W
  invFun := prodPull V W
  left_inv := prodPull_prodPush V W
  right_inv := prodPush_prodPull V W
  map_mul' := (prodPush V W).map_mul'
  map_add' := (prodPush V W).map_add'
  commutes' := (prodPush V W).commutes'

end ProdIso

end

end Work.KT

namespace Work.KT

open Matrix

noncomputable section

section Slice

variable (V W : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]

/-- `x ↦ (x, w₀) : D_V → D_{V×W}`, for `w₀` on the boundary of `D_W`. -/
def pairPtC (w₀ : Ball W) (hw₀ : w₀ ∈ bdry W) : C(Ball V, Ball (V × W)) :=
  ⟨fun x => ⟨((x : V), (w₀ : W)), by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      refine max_le ?_ hw₀.le
      simpa using (Metric.mem_closedBall.mp x.2 : dist (x : V) 0 ≤ 1)⟩, by fun_prop⟩

@[simp]
lemma pairPtC_apply (w₀ : Ball W) (hw₀ : w₀ ∈ bdry W) (x : Ball V) :
    (pairPtC V W w₀ hw₀ x : V × W) = ((x : V), (w₀ : W)) := rfl

/-- `y ↦ (v₀, y) : D_W → D_{V×W}`, for `v₀` on the boundary of `D_V`. -/
def pairPtD (v₀ : Ball V) (hv₀ : v₀ ∈ bdry V) : C(Ball W, Ball (V × W)) :=
  ⟨fun y => ⟨((v₀ : V), (y : W)), by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      refine max_le hv₀.le ?_
      simpa using (Metric.mem_closedBall.mp y.2 : dist (y : W) 0 ≤ 1)⟩, by fun_prop⟩

@[simp]
lemma pairPtD_apply (v₀ : Ball V) (hv₀ : v₀ ∈ bdry V) (y : Ball W) :
    (pairPtD V W v₀ hv₀ y : V × W) = ((v₀ : V), (y : W)) := rfl

/-- Every point of the slice `D_V × {w₀}` (`w₀ ∈ S_W`) lies on the boundary of `D_{V×W}`. -/
lemma pairPtC_mem_bdry (w₀ : Ball W) (hw₀ : w₀ ∈ bdry W) (x : Ball V) :
    pairPtC V W w₀ hw₀ x ∈ bdry (V × W) := by
  change ‖(((pairPtC V W w₀ hw₀ x : Ball (V × W)) : V × W))‖ = 1
  rw [pairPtC_apply, Prod.norm_def]
  show max ‖(x : V)‖ ‖(w₀ : W)‖ = 1
  have hx : ‖(x : V)‖ ≤ 1 := by
    simpa using (Metric.mem_closedBall.mp x.2 : dist (x : V) 0 ≤ 1)
  refine le_antisymm (max_le hx (le_of_eq hw₀)) ?_
  calc (1 : ℝ) = ‖(w₀ : W)‖ := hw₀.symm
    _ ≤ max ‖(x : V)‖ ‖(w₀ : W)‖ := le_max_right _ _

/-- Every point of the slice `{v₀} × D_W` (`v₀ ∈ S_V`) lies on the boundary of `D_{V×W}`. -/
lemma pairPtD_mem_bdry (v₀ : Ball V) (hv₀ : v₀ ∈ bdry V) (y : Ball W) :
    pairPtD V W v₀ hv₀ y ∈ bdry (V × W) := by
  change ‖(((pairPtD V W v₀ hv₀ y : Ball (V × W)) : V × W))‖ = 1
  rw [pairPtD_apply, Prod.norm_def]
  show max ‖(v₀ : V)‖ ‖(y : W)‖ = 1
  have hy : ‖(y : W)‖ ≤ 1 := by
    simpa using (Metric.mem_closedBall.mp y.2 : dist (y : W) 0 ≤ 1)
  refine le_antisymm (max_le (le_of_eq hv₀) hy) ?_
  calc (1 : ℝ) = ‖(v₀ : V)‖ := hv₀.symm
    _ ≤ max ‖(v₀ : V)‖ ‖(y : W)‖ := le_max_left _ _

/-- Restriction of a function in `prodAlg` to the slice `D_V × {w₀}`. -/
def sliceVFun (w₀ : Ball W) (hw₀ : w₀ ∈ bdry W) (F : prodAlg V W) : Kpair V :=
  ⟨(F : C(Ball (V × W), ℂ)).comp (pairPtC V W w₀ hw₀), by
    intro x hx x' hx'
    exact F.2.1 _ _ hx hx' rfl⟩

/-- Restriction of a function in `prodAlg` to the slice `{v₀} × D_W`. -/
def sliceWFun (v₀ : Ball V) (hv₀ : v₀ ∈ bdry V) (F : prodAlg V W) : Kpair W :=
  ⟨(F : C(Ball (V × W), ℂ)).comp (pairPtD V W v₀ hv₀), by
    intro y hy y' hy'
    exact F.2.2 _ _ hy hy' rfl⟩

/-- The algebra map `prodAlg V W → Kpair V` given by restriction to the slice `D_V × {w₀}`. -/
def sliceV (w₀ : Ball W) (hw₀ : w₀ ∈ bdry W) : prodAlg V W →ₐ[ℂ] Kpair V where
  toFun := sliceVFun V W w₀ hw₀
  map_one' := by apply Subtype.ext; apply ContinuousMap.ext; intro x; rfl
  map_mul' := by intro F G; apply Subtype.ext; apply ContinuousMap.ext; intro x; rfl
  map_zero' := by apply Subtype.ext; apply ContinuousMap.ext; intro x; rfl
  map_add' := by intro F G; apply Subtype.ext; apply ContinuousMap.ext; intro x; rfl
  commutes' := by intro c; apply Subtype.ext; apply ContinuousMap.ext; intro x; rfl

/-- The algebra map `prodAlg V W → Kpair W` given by restriction to the slice `{v₀} × D_W`. -/
def sliceW (v₀ : Ball V) (hv₀ : v₀ ∈ bdry V) : prodAlg V W →ₐ[ℂ] Kpair W where
  toFun := sliceWFun V W v₀ hv₀
  map_one' := by apply Subtype.ext; apply ContinuousMap.ext; intro y; rfl
  map_mul' := by intro F G; apply Subtype.ext; apply ContinuousMap.ext; intro y; rfl
  map_zero' := by apply Subtype.ext; apply ContinuousMap.ext; intro y; rfl
  map_add' := by intro F G; apply Subtype.ext; apply ContinuousMap.ext; intro y; rfl
  commutes' := by intro c; apply Subtype.ext; apply ContinuousMap.ext; intro y; rfl

end Slice

/-- The assertion of `Work.KT.ball_K` for a fixed normed space `V`, boundary point `y0` and `j`:
if `dim V = 2j` the reduced group is infinite cyclic with `ψ² = 2^j`, `ψ³ = 3^j`, and if
`dim V = 2j+1` the reduced group vanishes. -/
def BallKStmt (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (y0 : Ball V)
    (hy0 : y0 ∈ bdry V) (j : ℕ) : Prop :=
  (Module.finrank ℝ V = 2 * j →
    (∃ g : K0 (Kpair V), K0.mapA (augPair V y0) g = 0 ∧ (∀ k : ℤ, k • g = 0 → k = 0) ∧
      ∀ z : K0 (Kpair V), K0.mapA (augPair V y0) z = 0 → ∃ k : ℤ, z = k • g) ∧
    (∀ ψ : K0 (Kpair V) →+ K0 (Kpair V), IsPsi2 ψ →
      ∀ z : K0 (Kpair V), K0.mapA (augPair V y0) z = 0 → ψ z = (2 ^ j : ℤ) • z) ∧
    (∀ ψ : K0 (Kpair V) →+ K0 (Kpair V), IsPsi3 ψ →
      ∀ z : K0 (Kpair V), K0.mapA (augPair V y0) z = 0 → ψ z = (3 ^ j : ℤ) • z)) ∧
  (Module.finrank ℝ V = 2 * j + 1 → ∀ z : K0 (Kpair V), K0.mapA (augPair V y0) z = 0 → z = 0)

end

end Work.KT
