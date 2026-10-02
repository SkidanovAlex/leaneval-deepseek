import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.Serre.Models
import Submission.Work.StemsB.PiMap
import Submission.Work.Serre.exists_path_pullbackFst
import Submission.Work.Serre.hZeroOfPiZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre.Assembly

/-- naturality of `genLoopEquivOfUnique` under postcomposition. -/
theorem genLoopEquivOfUnique_genLoopMap {Γ B : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    (g : C(Γ, B)) {γ : Γ} (w : Ω^ (Fin 1) Γ γ) :
    genLoopEquivOfUnique (Fin 1) (Work.StemsB.genLoopMap g 1 w)
      = (genLoopEquivOfUnique (Fin 1) w).map g.continuous := by
  ext t
  rfl

/-- Surjectivity of `π₁(g)` produces, for every loop `c` in `B` at `g γ`, a loop `ξ` in `Γ` at `γ`
whose image under `g` is homotopic to `c`. -/
theorem exists_path_of_pi1_surjective {Γ B : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    (g : C(Γ, B)) {γ : Γ} (h : Function.Surjective (Work.Serre.piMapN g 1 γ))
    (c : Path (g γ) (g γ)) : ∃ ξ : Path γ γ, Path.Homotopic (ξ.map g.continuous) c := by
  set c₀ : Ω^ (Fin 1) B (g γ) := (genLoopEquivOfUnique (Fin 1)).symm c with hc₀
  obtain ⟨a, ha⟩ := h (⟦c₀⟧ : π_ 1 B (g γ))
  induction a using Quotient.inductionOn with
  | h w =>
    refine ⟨genLoopEquivOfUnique (Fin 1) w, ?_⟩
    have h1 : (⟦Work.StemsB.genLoopMap g 1 w⟧ : π_ 1 B (g γ)) = ⟦c₀⟧ := by
      rw [← Work.Serre.piMapN_apply_mk]
      exact ha
    have h2 : (⟦(genLoopEquivOfUnique (Fin 1) w).map g.continuous⟧ :
        Path.Homotopic.Quotient (g γ) (g γ)) = ⟦c⟧ := by
      have h3 := congrArg (HomotopyGroup.pi1EquivFundamentalGroup (x := g γ)) h1
      rw [show HomotopyGroup.pi1EquivFundamentalGroup (x := g γ)
            (⟦Work.StemsB.genLoopMap g 1 w⟧ : π_ 1 B (g γ))
            = ⟦genLoopEquivOfUnique (Fin 1) (Work.StemsB.genLoopMap g 1 w)⟧ from rfl,
          genLoopEquivOfUnique_genLoopMap] at h3
      rw [show HomotopyGroup.pi1EquivFundamentalGroup (x := g γ) (⟦c₀⟧ : π_ 1 B (g γ))
            = ⟦genLoopEquivOfUnique (Fin 1) c₀⟧ from rfl, hc₀, Equiv.apply_symm_apply] at h3
      exact h3
    exact Path.Homotopic.Quotient.eq.mp h2

/-- A point of the boundary of the `1`-cube has its only coordinate at `0` or at `1`. -/
lemma cubeBdry_one_zero_or_one (x : Work.StemsB.CubeBdry 1) : x.1 0 = 0 ∨ x.1 0 = 1 := by
  obtain ⟨i, hi⟩ := x.2
  have hi0 : i = 0 := Subsingleton.elim i 0
  subst hi0
  exact hi

/-- `(1 : I) ≠ 0`. -/
lemma one_ne_zero_I : ¬ ((1 : I) = 0) := by
  intro h
  have h2 : (((1 : I) : ℝ)) = (((0 : I) : ℝ)) := congrArg (fun z : I => (z : ℝ)) h
  norm_num at h2

/-- **Injectivity of the base change on path components.**  Two points of the fibre product whose
images in `E` are joined by a path are themselves joined in the fibre product.

The path `α` in `E` projects to a path `p ∘ α` in `B`; the surjectivity of `π₁(g)` at `γ` allows one
to replace the path `ζ₀` from `γ` to `γ'` by a path `ζ` whose image under `g` is homotopic to
`p ∘ α` relative to the endpoints.  A relative homotopy lifting (`Work.StemsB.exists_lift_rel`,
lateral boundary prescribed as the constants `e` and `e'`) then produces a lift `β` of `g ∘ ζ`
starting at `e`; because the relative lifting property fixes the lateral boundary, `β` ends at
`e'` — the plain absolute homotopy lifting property would let the lift drift along the fibre.  Then
`t ↦ (ζ t, β t)` is the required path in the fibre product. -/
theorem joined_pullbackSnd {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    {γ γ' : Γ} {e e' : E} (hx : g γ = p e) (hx' : g γ' = p e')
    (hγ : Joined γ γ') (h1 : Function.Surjective (Work.Serre.piMapN g 1 γ))
    (hα : Joined e e') :
    Joined (⟨(γ, e), hx⟩ : Work.StemsB.Pullback g p) ⟨(γ', e'), hx'⟩ := by
  classical
  obtain ⟨α⟩ := hα
  obtain ⟨ζ₀⟩ := hγ
  let δ : Path (g γ) (g γ') := (α.map p.continuous).cast hx hx'
  let A : Path (g γ) (g γ') := ζ₀.map g.continuous
  let c : Path (g γ) (g γ) := δ.trans A.symm
  obtain ⟨ξ, hξ⟩ := exists_path_of_pi1_surjective g h1 c
  let ζ : Path γ γ' := ξ.trans ζ₀
  have hmap : Path.Homotopic (ζ.map g.continuous) δ := by
    have h2 : Path.Homotopic ((ξ.map g.continuous).trans A) ((δ.trans A.symm).trans A) :=
      hξ.hcomp (Path.Homotopic.refl A)
    have h3 : Path.Homotopic ((δ.trans A.symm).trans A) δ :=
      (Path.Homotopic.trans_assoc δ A.symm A).trans
        (((Path.Homotopic.refl δ).hcomp (Path.Homotopic.symm_trans A)).trans
          (Path.Homotopic.trans_refl δ))
    have h4 : Path.Homotopic (ζ.map g.continuous) ((ξ.map g.continuous).trans A) := by
      have e1 : ζ.map g.continuous = (ξ.map g.continuous).trans A := by
        show (ξ.trans ζ₀).map g.continuous = (ξ.map g.continuous).trans (ζ₀.map g.continuous)
        exact Path.map_trans ξ ζ₀ (f := ⇑g) g.continuous
      rw [e1]
    exact h4.trans (h2.trans h3)
  obtain ⟨F⟩ := hmap.symm
  let f : C(Fin 1 → I, E) := ⟨fun z => α (z 0), α.continuous.comp (continuous_apply 0)⟩
  let HH : C((Fin 1 → I) × I, B) := ⟨fun w => F (w.2, w.1 0), by fun_prop⟩
  have hf : p.comp f = HH.comp (Work.StemsB.zeroIncl 1) := by
    ext z
    show p (α (z 0)) = HH (z, 0)
    show p (α (z 0)) = F (0, z 0)
    exact (F.map_zero_left (z 0)).symm
  have hcontI : Continuous fun w : Work.StemsB.CubeBdry 1 × I => w.1.1 0 :=
    (continuous_apply 0).comp (continuous_subtype_val.comp continuous_fst)
  have hcontR : Continuous fun w : Work.StemsB.CubeBdry 1 × I => ((w.1.1 0 : I) : ℝ) :=
    continuous_subtype_val.comp hcontI
  have hiff0 : ∀ w : Work.StemsB.CubeBdry 1 × I, (w.1.1 0 = 0) ↔ ((w.1.1 0 : I) : ℝ) < 1/2 := by
    intro w
    constructor
    · intro h; rw [h]; norm_num
    · intro h
      rcases cubeBdry_one_zero_or_one w.1 with h' | h'
      · exact h'
      · rw [h'] at h; norm_num at h
  have hclosed0 : IsClosed {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0} :=
    isClosed_eq hcontI continuous_const
  have hopen0 : IsOpen {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0} := by
    rw [show {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0}
        = {w : Work.StemsB.CubeBdry 1 × I | ((w.1.1 0 : I) : ℝ) < 1/2} from Set.ext hiff0]
    exact isOpen_lt hcontR continuous_const
  have hfront : frontier {w : Work.StemsB.CubeBdry 1 × I | w.1.1 0 = 0} = ∅ := by
    rw [frontier_eq_closure_inter_closure, hclosed0.closure_eq, hopen0.isClosed_compl.closure_eq,
      Set.inter_compl_self]
  have hgdcont : Continuous fun w : Work.StemsB.CubeBdry 1 × I =>
      if w.1.1 0 = 0 then e else e' :=
    Continuous.if (fun a ha => absurd ha (by rw [hfront]; exact Set.notMem_empty a))
      continuous_const continuous_const
  let gd : C(Work.StemsB.CubeBdry 1 × I, E) :=
    ⟨fun w => if w.1.1 0 = 0 then e else e', hgdcont⟩
  have hne : ∀ x : Work.StemsB.CubeBdry 1, x.1 0 = 1 → ¬ (x.1 0 = 0) := by
    intro x hx0 h0
    rw [hx0] at h0
    exact one_ne_zero_I h0
  have hg : p.comp gd = HH.comp (Work.StemsB.bdryIncl 1) := by
    ext w
    obtain ⟨x, t⟩ := w
    show p (if x.1 0 = 0 then e else e') = HH (x.1, t)
    show p (if x.1 0 = 0 then e else e') = F (t, x.1 0)
    rcases cubeBdry_one_zero_or_one x with h | h
    · rw [if_pos h, h]
      rw [show F (t, 0) = δ 0 from F.prop' t 0 (by simp), show δ 0 = g γ from δ.source]
      exact hx.symm
    · rw [if_neg (hne x h), h]
      rw [show F (t, 1) = δ 1 from F.prop' t 1 (by simp), show δ 1 = g γ' from δ.target]
      exact hx'.symm
  have hg0 : ∀ x : Work.StemsB.CubeBdry 1, gd (x, 0) = f x.1 := by
    intro x
    show (if x.1 0 = 0 then e else e') = α (x.1 0)
    rcases cubeBdry_one_zero_or_one x with h | h
    · rw [if_pos h, h]
      show e = α 0
      exact (α.source).symm
    · rw [if_neg (hne x h), h]
      show e' = α 1
      exact (α.target).symm
  obtain ⟨G, hGp, hG0, hGlat⟩ := Work.StemsB.exists_lift_rel p hp 1 HH f hf gd hg hg0
  let z0 : Fin 1 → I := fun _ => 0
  let z1 : Fin 1 → I := fun _ => 1
  have hz0 : z0 ∈ Cube.boundary (Fin 1) := ⟨0, Or.inl rfl⟩
  have hz1 : z1 ∈ Cube.boundary (Fin 1) := ⟨0, Or.inr rfl⟩
  have hz10 : ¬ ((z1 : Fin 1 → I) 0 = 0) := fun h => one_ne_zero_I h
  let β : Path e e' :=
    Path.mk ⟨fun t : I => G ((fun _ => t), 1), by fun_prop⟩
      (by
        show G (z0, 1) = e
        rw [show G (z0, 1) = gd (⟨z0, hz0⟩, 1) from hGlat ⟨z0, hz0⟩ 1]
        show (if (z0 : Fin 1 → I) 0 = 0 then e else e') = e
        rw [if_pos rfl])
      (by
        show G (z1, 1) = e'
        rw [show G (z1, 1) = gd (⟨z1, hz1⟩, 1) from hGlat ⟨z1, hz1⟩ 1]
        show (if (z1 : Fin 1 → I) 0 = 0 then e else e') = e'
        rw [if_neg hz10])
  have hpt : ∀ t : I, g (ζ t) = p (β t) := by
    intro t
    have h1 : p (G ((fun _ => t), 1)) = HH ((fun _ => t), 1) :=
      congrFun (congrArg DFunLike.coe hGp) ((fun _ => t), 1)
    have h2 : HH ((fun _ => t), 1) = g (ζ t) := by
      show F (1, t) = g (ζ t)
      exact F.map_one_left t
    exact (h1.trans h2).symm
  refine ⟨Path.mk ⟨fun t => ⟨(ζ t, β t), hpt t⟩, ?_⟩ ?_ ?_⟩
  · exact Continuous.subtype_mk (ζ.continuous.prodMk β.continuous) hpt
  · exact Subtype.ext (Prod.ext ζ.source β.source)
  · exact Subtype.ext (Prod.ext ζ.target β.target)

/-- `piMapN f 0 x` is bijective iff the induced map on path components is. -/
theorem bijective_piMapN_zero_iff_h0Pi0Map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    Function.Bijective (Work.Serre.piMapN f 0 x) ↔ Function.Bijective (h0Pi0Map f) := by
  constructor
  · exact h0Pi0Map_bijective f
  · intro hb
    have hfun : Work.Serre.piMapN f 0 x =
        ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f x)).symm ∘
          (h0Pi0Map f ∘ ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x))) := by
      funext a
      simp only [Function.comp_apply]
      exact (Equiv.eq_symm_apply
        (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f x))).mpr
        (h0Pi0Map_square (x₀ := x) f a).symm
    rw [hfun]
    exact Function.Bijective.comp
      (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f x)).symm.bijective
      (hb.comp (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).bijective)

/-- Surjectivity on path components from pointwise reachability. -/
theorem surjective_h0Pi0Map_of_joined {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (h : ∀ y : Y, ∃ x : X, Joined (f x) y) :
    Function.Surjective (h0Pi0Map f) := by
  intro c
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨x, ⟨p⟩⟩ := h y
  exact ⟨ZerothHomotopy.mk x, by rw [h0Pi0Map_mk]; exact ZerothHomotopy.sound p⟩

/-- Injectivity on path components from injectivity of the pointwise relation. -/
theorem injective_h0Pi0Map_of_joined {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (h : ∀ x x' : X, Joined (f x) (f x') → Joined x x') :
    Function.Injective (h0Pi0Map f) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
  obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
  rw [h0Pi0Map_mk, h0Pi0Map_mk] at hab
  obtain ⟨p⟩ := h x y (Quotient.exact hab)
  exact ZerothHomotopy.sound p

-- **The `π₀` case of the base change of a fibration along a connected map.**
--
-- `p : E → B` a Serre fibration, `g : Γ → B` with `π₁(g)` surjective at every point, `Γ` and `B`
-- path connected.  Then `pullbackSnd g p : Γ ×_B E → E` induces a *bijection* on `π₀`
-- (`Work.Serre.piMapN · 0`, i.e. `π₀(-,x) ≃ π₀(-)`).
--
-- Surjectivity: `p` is surjective (path lifting: `hp 0` is the homotopy lifting property with
-- respect to a point), so every path component of `E` meets `p⁻¹{b₀}`, and `p⁻¹{b₀}` is contained
-- in the image of `pullbackSnd g p` (take `γ₀` with `g γ₀ = b₀`).
--
-- Injectivity: let `x = (γ,e)`, `x' = (γ',e')` in `Γ ×_B E` with `r x`, `r x'` joined in `E`,
-- where `r = pullbackSnd g p`.  Take a path `α` in `E` from `e` to `e'`; then `δ := p ∘ α` is a
-- path in `B` from `g γ` to `g γ'`.  Choose a path `ζ₀` from `γ` to `γ'` in `Γ` (Γ is path
-- connected) and use surjectivity of `π₁(g)` at `γ` to find a loop `ξ` at `γ` with
-- `g ∘ ξ` homotopic to `δ * (g ∘ ζ₀)⁻¹` relative to the endpoints; then `ζ := ξ * ζ₀` satisfies
-- `g ∘ ζ ~ p ∘ α` relative to the endpoints.  Lift that homotopy through `p` using the relative
-- homotopy lifting property `Work.StemsB.HasHLPRel p 1` (`Work.StemsB.exists_lift_rel`), with the
-- lateral boundary lifts specified as the constants `e` and `e'` (compatible with `α 0 = e` and
-- `α 1 = e'`) — the plain absolute lifting property is *not* enough, since the lifted left edge
-- can drift away from `e'`.  The lifted homotopy gives a path `β'` in `E` from `e` to `e'` with
-- `p (β'_t) = g (ζ_t)`, and then `t ↦ (ζ_t, β'_t)` is a path in `Γ ×_B E` from `x` to `x'`. -/
theorem pullbackSnd_piMapN_zero_bijective {Γ B E : Type} [TopologicalSpace Γ]
    [TopologicalSpace B] [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p)
    (hg1 : ∀ x : Γ, Function.Bijective (Work.Serre.piMapN g 1 x))
    (hΓ : PathConnectedSpace Γ) (hB : PathConnectedSpace B) :
    ∀ x : Work.StemsB.Pullback g p,
      Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackSnd g p) 0 x) := by
  classical
  have hsurj : ∀ e : E, ∃ y : Work.StemsB.Pullback g p,
      Joined (Work.StemsB.pullbackSnd g p y) e := by
    intro e
    obtain ⟨γ₀⟩ := hΓ.nonempty
    obtain ⟨pp⟩ := hB.joined (p e) (g γ₀)
    obtain ⟨e', he', ⟨α⟩⟩ := Work.Serre.exists_path_lift_of_isSerreFibration p hp rfl pp
    exact ⟨⟨(γ₀, e'), he'.symm⟩, ⟨α.symm⟩⟩
  have hinj : ∀ x x' : Work.StemsB.Pullback g p,
      Joined (Work.StemsB.pullbackSnd g p x) (Work.StemsB.pullbackSnd g p x') →
        Joined x x' := by
    intro x x' hj
    exact joined_pullbackSnd g p hp x.2 x'.2 (hΓ.joined x.1.1 x'.1.1) (hg1 x.1.1).2 hj
  have key : Function.Bijective (h0Pi0Map (Work.StemsB.pullbackSnd g p)) :=
    ⟨injective_h0Pi0Map_of_joined _ hinj, surjective_h0Pi0Map_of_joined _ hsurj⟩
  intro x
  exact (bijective_piMapN_zero_iff_h0Pi0Map _ x).mpr key


end Work.Serre.Assembly
