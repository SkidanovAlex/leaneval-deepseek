import Mathlib
import Submission.Work.ThomBordism.TwoSet.CubeCollapse
import Submission.Work.ThomBordism.TwoSet.SphereExtensionBase

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pushing lemma: deforming a disc with boundary in `Z` into `Z`

If `Y` has trivial `π_e` (at every basepoint) and `Z ⊆ Y` has trivial `π_{e-1}`, then any continuous
`σ : I^e → Y` sending `∂I^e` into `Z` is homotopic, relative to `∂I^e`, to a map into `Z`.

The proof glues `σ` with an extension of `σ|∂I^e` into `Z` (which exists because `π_{e-1}(Z) = 0`),
obtaining a map `Δ : ∂I^{e+1} → Y` ("`σ` on the top face, the extension on the bottom face, and
`σ|∂I^e` on the collar").  The composite `Δ ∘ Θ` with the collapse `Θ : I^e → ∂I^{e+1}` is a
genuine based cube map, hence null-homotopic by `π_e(Y) = 0`; descending that homotopy along
`Θ × id` shows that `Δ` is null-homotopic, and the coning lemma `ConeDescent` then extends `Δ` over
`I^{e+1}`, which is exactly the desired homotopy.
-/

namespace Work.ThomBordism.TwoSet

open scoped Topology unitInterval

/-- **Descent of a homotopy along the collapse.**  A homotopy `H` on `I^d × I` which is constant on
the boundary slice `∂I^d × {t}` descends to a homotopy on `∂I^{d+1} × I` along `Θ × id`. -/
theorem exists_descend_homotopy {Y : Type*} [TopologicalSpace Y] {d : ℕ} (hd : 1 ≤ d)
    (Θ : C(IC d, {x : IC (d+1) // x ∈ Cube.boundary (Fin (d+1))}))
    (hΘq : Topology.IsQuotientMap Θ)
    (hfib : ∀ x y, Θ x = Θ y →
      x = y ∨ (x ∈ Cube.boundary (Fin d) ∧ y ∈ Cube.boundary (Fin d)))
    (H : C(IC d × I, Y))
    (hHbd : ∀ x ∈ Cube.boundary (Fin d), ∀ x' ∈ Cube.boundary (Fin d), ∀ t : I,
      H (x, t) = H (x', t)) :
    ∃ H' : C({x : IC (d+1) // x ∈ Cube.boundary (Fin (d+1))} × I, Y),
      ∀ x t, H' (Θ x, t) = H (x, t) := by
  have hcont : Continuous fun p : IC d × I =>
      ((Θ p.1, p.2) : {x : IC (d+1) // x ∈ Cube.boundary (Fin (d+1))} × I) :=
    (Θ.continuous.comp continuous_fst).prodMk continuous_snd
  let q : C(IC d × I, {x : IC (d+1) // x ∈ Cube.boundary (Fin (d+1))} × I) :=
    ⟨fun p => (Θ p.1, p.2), hcont⟩
  have hsurj : Function.Surjective q := by
    rintro ⟨w, t⟩
    obtain ⟨x, rfl⟩ := hΘq.surjective w
    exact ⟨(x, t), rfl⟩
  have hcl : IsClosedMap q := fun s hs => (hs.isCompact.image q.continuous).isClosed
  have hq : Topology.IsQuotientMap q := hcl.isQuotientMap q.continuous hsurj
  have hfac : Function.FactorsThrough H q := by
    intro p p' hpp
    have h2 : p.2 = p'.2 := (Prod.ext_iff.mp hpp).2
    have h1 : Θ p.1 = Θ p'.1 := (Prod.ext_iff.mp hpp).1
    rcases hfib p.1 p'.1 h1 with h | ⟨hp, hp'⟩
    · rw [Prod.ext_iff.mpr ⟨h, h2⟩]
    · show H p = H p'
      have hstep : H (p.1, p.2) = H (p'.1, p.2) := hHbd p.1 hp p'.1 hp' p.2
      rw [hstep, h2]
  have hlc : (hq.lift H hfac).comp q = H := hq.lift_comp H hfac
  refine ⟨hq.lift H hfac, fun x t => ?_⟩
  have h := congrFun (congrArg (fun k : C(IC d × I, Y) => ⇑k) hlc) (x, t)
  show (hq.lift H hfac) ((fun p : IC d × I => (Θ p.1, p.2)) (x, t)) = H (x, t)
  exact h

/-- A map `∂I^{m+1} → Z` extends over the cube when `π_m (Z) = 0` at every basepoint. -/
theorem exists_extension_succ {Z : Type*} [TopologicalSpace Z] {m : ℕ}
    (hZ : ∀ z : Z, Subsingleton (HomotopyGroup (Fin m) Z z))
    (f : C({x : IC (m+1) // x ∈ Cube.boundary (Fin (m+1))}, Z)) :
    ∃ g : C(IC (m+1), Z), ∀ x, g x.1 = f x := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    obtain ⟨Ψ, hΨ⟩ := SphereExtensionBase (Y := Z) hZ f
    exact ⟨Ψ, fun x => congrFun (congrArg DFunLike.coe hΨ) x⟩
  · obtain ⟨Θ, hΘbd, hΘsurj, hΘq, hΘfib⟩ := cubeBoundaryCollapse m hpos
    let p : GenLoop (Fin m) Z (f (Θ 0)) :=
      ⟨⟨fun y => f (Θ y), f.continuous.comp Θ.continuous⟩, fun y hy => by
        show f (Θ y) = f (Θ 0)
        rw [hΘbd y hy]⟩
    haveI : Subsingleton (HomotopyGroup (Fin m) Z (f (Θ 0))) := hZ (f (Θ 0))
    have hpp : (⟦p⟧ : HomotopyGroup (Fin m) Z (f (Θ 0))) = ⟦GenLoop.const⟧ :=
      (hZ (f (Θ 0))).elim _ _
    have hhom : GenLoop.Homotopic p GenLoop.const := Quotient.exact hpp
    obtain ⟨Hp, hprop⟩ := hhom
    let Hpc : C(IC m × I, Z) :=
      ⟨fun q => Hp (q.2, q.1),
        Hp.continuous_toFun.comp (continuous_snd.prodMk continuous_fst)⟩
    have hHpc : ∀ (y : IC m) (t : I), Hpc (y, t) = Hp (t, y) := fun _ _ => rfl
    obtain ⟨H', hH'⟩ := exists_descend_homotopy hpos Θ hΘq hΘfib Hpc
      (fun y hy y' hy' t => by
        rw [hHpc y t, hHpc y' t]
        exact (hprop t y hy).trans ((p.2 y hy).trans ((p.2 y' hy').symm.trans
          (hprop t y' hy').symm)))
    have h0 : ∀ w, H' (w, 0) = f w := by
      intro w
      obtain ⟨y, rfl⟩ := hΘsurj w
      rw [hH' y 0, hHpc y 0]; exact Hp.map_zero_left y
    have h1c : ∀ w, H' (w, 1) = f (Θ 0) := by
      intro w
      obtain ⟨y, rfl⟩ := hΘsurj w
      rw [hH' y 1, hHpc y 1]; exact Hp.map_one_left y
    obtain ⟨Ψ, hΨ⟩ := ConeDescent (by omega : 1 ≤ m + 1) H' h1c
    exact ⟨Ψ, fun x => by rw [hΨ x, h0 x]⟩

/-- The map glued from `g` (on the face `t = 1`) and `sig` (on the rest of the boundary). -/
noncomputable def gluedFun {Y : Type*} {m : ℕ} (g sig : IC (m+1) → Y) (x : IC (m+2)) : Y :=
  if x (Fin.last (m+1)) = 1 then g (Fin.init x) else sig (Fin.init x)

theorem gluedFun_pos {Y : Type*} {m : ℕ} (g sig : IC (m+1) → Y) {x : IC (m+2)}
    (h : x (Fin.last (m+1)) = 1) : gluedFun g sig x = g (Fin.init x) := if_pos h

theorem gluedFun_neg {Y : Type*} {m : ℕ} (g sig : IC (m+1) → Y) {x : IC (m+2)}
    (h : ¬ (x (Fin.last (m+1)) = 1)) : gluedFun g sig x = sig (Fin.init x) := if_neg h

/-- **The pushing lemma.** -/
theorem push_into_Z {Y : Type*} [TopologicalSpace Y] {Z : Set Y} {e : ℕ} (he : 1 ≤ e)
    (hY : ∀ y : Y, Subsingleton (HomotopyGroup (Fin e) Y y))
    (hZ : ∀ z : ↥Z, Subsingleton (HomotopyGroup (Fin (e-1)) ↥Z z))
    (sig : C(IC e, Y)) (hsig : ∀ x ∈ Cube.boundary (Fin e), sig x ∈ Z) :
    ∃ (g : C(IC e, Y)) (K : C(IC e × I, Y)),
      (∀ x, K (x, 0) = sig x) ∧
      (∀ x (_ : x ∈ Cube.boundary (Fin e)) t, K (x, t) = sig x) ∧
      (∀ x, g x ∈ Z) ∧ (∀ x (_ : x ∈ Cube.boundary (Fin e)), g x = sig x) ∧
      (∀ x, K (x, 1) = g x) := by
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
  -- (1) extend the boundary into `Z`
  let α : C({x : IC (m+1) // x ∈ Cube.boundary (Fin (m+1))}, ↥Z) :=
    ⟨fun x => ⟨sig x.1, hsig x.1 x.2⟩,
      Continuous.subtype_mk (sig.continuous.comp continuous_subtype_val) _⟩
  obtain ⟨gZ, hgZ⟩ := exists_extension_succ hZ α
  let g : C(IC (m+1), Y) :=
    ⟨fun x => (gZ x : Y), continuous_subtype_val.comp gZ.continuous⟩
  have hgsig : ∀ x (hx : x ∈ Cube.boundary (Fin (m+1))), g x = sig x := fun x hx =>
    congrArg Subtype.val (hgZ ⟨x, hx⟩)
  -- (2) the glued map on `∂I^{m+2}`
  let Δfun : IC (m+2) → Y := fun x => gluedFun (⇑g) (⇑sig) x
  have hinitcont : Continuous (Fin.init : IC (m+2) → IC (m+1)) :=
    continuous_pi (fun i => continuous_apply i.castSucc)
  have h1 : ContinuousOn Δfun
      ({x : IC (m+2) | x (Fin.last (m+1)) = 1} ∩ Cube.boundary (Fin (m+2))) := by
    refine ((g.continuous.comp hinitcont).continuousOn).congr (fun x hx => ?_)
    show gluedFun (⇑g) (⇑sig) x = g (Fin.init x)
    exact gluedFun_pos _ _ hx.1
  have h2 : ContinuousOn Δfun
      (({x : IC (m+2) | x (Fin.last (m+1)) = 0} ∪
        {x : IC (m+2) | Fin.init x ∈ Cube.boundary (Fin (m+1))}) ∩
          Cube.boundary (Fin (m+2))) := by
    refine ((sig.continuous.comp hinitcont).continuousOn).congr (fun x hx => ?_)
    show gluedFun (⇑g) (⇑sig) x = sig (Fin.init x)
    rcases hx.1 with h0 | ht
    · exact gluedFun_neg _ _ (by rw [h0]; exact zero_ne_one)
    · by_cases h : x (Fin.last (m+1)) = 1
      · rw [gluedFun_pos _ _ h]
        exact hgsig (Fin.init x) ht
      · exact gluedFun_neg _ _ h
  have hcover : ({x : IC (m+2) | x (Fin.last (m+1)) = 1} ∩ Cube.boundary (Fin (m+2))) ∪
      (({x : IC (m+2) | x (Fin.last (m+1)) = 0} ∪
        {x : IC (m+2) | Fin.init x ∈ Cube.boundary (Fin (m+1))}) ∩
          Cube.boundary (Fin (m+2))) = Cube.boundary (Fin (m+2)) := by
    ext x
    constructor
    · intro hx; rcases hx with hx | hx <;> exact hx.2
    · intro hx
      by_cases h : x (Fin.last (m+1)) = 1
      · exact Or.inl ⟨h, hx⟩
      · right
        refine ⟨?_, hx⟩
        obtain ⟨i, hi⟩ := hx
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | hlast
        · right; exact ⟨j, hi⟩
        · left; rw [hlast] at hi
          rcases hi with h' | h'
          · exact h'
          · exact absurd h' h
  have hΔcont : ContinuousOn Δfun (Cube.boundary (Fin (m+2))) := by
    have hK1 : IsClosed ({x : IC (m+2) | x (Fin.last (m+1)) = 1} ∩
        Cube.boundary (Fin (m+2))) :=
      (isClosed_eq (continuous_apply _) continuous_const).inter (isClosed_cubeBoundary _)
    have hK2 : IsClosed (({x : IC (m+2) | x (Fin.last (m+1)) = 0} ∪
        {x : IC (m+2) | Fin.init x ∈ Cube.boundary (Fin (m+1))}) ∩
          Cube.boundary (Fin (m+2))) :=
      ((isClosed_eq (continuous_apply _) continuous_const).union
        ((isClosed_cubeBoundary (m+1)).preimage hinitcont)).inter (isClosed_cubeBoundary _)
    have h := ContinuousOn.union_of_isClosed h1 h2 hK1 hK2
    rwa [hcover] at h
  have hΔcont' : Continuous (Set.domRestrict (Cube.boundary (Fin (m+2))) Δfun) :=
    (continuousOn_iff_continuous_domRestrict).mp hΔcont
  let Δ : C({x : IC (m+2) // x ∈ Cube.boundary (Fin (m+2))}, Y) :=
    ⟨fun x => Δfun x.1, hΔcont'.congr (fun x => rfl)⟩
  -- (3) `Δ` is null-homotopic
  obtain ⟨Θ, hΘbd, hΘsurj, hΘq, hΘfib⟩ := cubeBoundaryCollapse (m+1) (by omega)
  let p : GenLoop (Fin (m+1)) Y (Δ (Θ 0)) :=
    ⟨⟨fun y => Δ (Θ y), Δ.continuous.comp Θ.continuous⟩,
      fun y hy => by
        show Δ (Θ y) = Δ (Θ 0)
        rw [hΘbd y hy]⟩
  haveI : Subsingleton (HomotopyGroup (Fin (m+1)) Y (Δ (Θ 0))) := hY _
  have hpp : (⟦p⟧ : HomotopyGroup (Fin (m+1)) Y (Δ (Θ 0))) = ⟦GenLoop.const⟧ :=
    (hY (Δ (Θ 0))).elim _ _
  have hhom : GenLoop.Homotopic p GenLoop.const := Quotient.exact hpp
  obtain ⟨Hp, hprop⟩ := hhom
  let Hpc : C(IC (m+1) × I, Y) :=
    ⟨fun q => Hp (q.2, q.1),
      Hp.continuous_toFun.comp (continuous_snd.prodMk continuous_fst)⟩
  have hHpc : ∀ (y : IC (m+1)) (t : I), Hpc (y, t) = Hp (t, y) := fun _ _ => rfl
  obtain ⟨H', hH'⟩ := exists_descend_homotopy (by omega : 1 ≤ m + 1) Θ hΘq hΘfib Hpc
    (fun y hy y' hy' t => by
      rw [hHpc y t, hHpc y' t]
      exact (hprop t y hy).trans ((p.2 y hy).trans ((p.2 y' hy').symm.trans
        (hprop t y' hy').symm)))
  have hΔ0 : ∀ w, H' (w, 0) = Δ w := by
    intro w
    obtain ⟨y, rfl⟩ := hΘsurj w
    rw [hH' y 0, hHpc y 0]; exact Hp.map_zero_left y
  have hΔ1 : ∀ w, H' (w, 1) = Δ (Θ 0) := by
    intro w
    obtain ⟨y, rfl⟩ := hΘsurj w
    rw [hH' y 1, hHpc y 1]; exact Hp.map_one_left y
  -- (4) extend `Δ` over the cube
  obtain ⟨Ψ, hΨ⟩ := ConeDescent (by omega : 1 ≤ m + 2) H' hΔ1
  have hΨΔ : ∀ w : {x : IC (m+2) // x ∈ Cube.boundary (Fin (m+2))}, Ψ w.1 = Δ w :=
    fun w => by rw [hΨ w, hΔ0 w]
  -- (5) assemble
  have hsnoct : Continuous fun q : IC (m+1) × I => (@Fin.snoc (m+1) (fun _ => unitInterval) q.1 q.2) := by
    refine continuous_pi (fun j => ?_)
    refine Fin.lastCases ?_ (fun i => ?_) j
    · have hfun : (fun q : IC (m+1) × I =>
          (@Fin.snoc (m+1) (fun _ => unitInterval) q.1 q.2) (Fin.last (m+1))) = fun q => q.2 := by
        funext q; rw [Fin.snoc_last]
      rw [hfun]
      exact continuous_snd
    · have hfun : (fun q : IC (m+1) × I =>
          (@Fin.snoc (m+1) (fun _ => unitInterval) q.1 q.2) (Fin.castSucc i)) = fun q => q.1 i := by
        funext q; rw [Fin.snoc_castSucc]
      rw [hfun]
      exact (continuous_apply i).comp continuous_fst
  let K : C(IC (m+1) × I, Y) :=
    ⟨fun q => Ψ (@Fin.snoc (m+1) (fun _ => unitInterval) q.1 q.2), Ψ.continuous.comp hsnoct⟩
  have hK0 : ∀ x, K (x, 0) = sig x := by
    intro x
    have hlast : (@Fin.snoc (m+1) (fun _ => unitInterval) x (0 : I)) (Fin.last (m+1)) = 0 :=
      Fin.snoc_last ..
    have hinit : Fin.init (@Fin.snoc (m+1) (fun _ => unitInterval) x (0 : I)) = x := Fin.init_snoc ..
    have hmem : (@Fin.snoc (m+1) (fun _ => unitInterval) x (0 : I)) ∈
        Cube.boundary (Fin (m+2)) := ⟨Fin.last (m+1), Or.inl hlast⟩
    show Ψ (@Fin.snoc (m+1) (fun _ => unitInterval) x (0 : I)) = sig x
    rw [hΨΔ ⟨@Fin.snoc (m+1) (fun _ => unitInterval) x (0 : I), hmem⟩]
    show gluedFun (⇑g) (⇑sig) (@Fin.snoc (m+1) (fun _ => unitInterval) x (0 : I)) = sig x
    rw [gluedFun_neg _ _ (by rw [hlast]; exact zero_ne_one), hinit]
  have hK1 : ∀ x, K (x, 1) = g x := by
    intro x
    have hlast : (@Fin.snoc (m+1) (fun _ => unitInterval) x (1 : I)) (Fin.last (m+1)) = 1 :=
      Fin.snoc_last ..
    have hinit : Fin.init (@Fin.snoc (m+1) (fun _ => unitInterval) x (1 : I)) = x := Fin.init_snoc ..
    have hmem : (@Fin.snoc (m+1) (fun _ => unitInterval) x (1 : I)) ∈
        Cube.boundary (Fin (m+2)) := ⟨Fin.last (m+1), Or.inr hlast⟩
    show Ψ (@Fin.snoc (m+1) (fun _ => unitInterval) x (1 : I)) = g x
    rw [hΨΔ ⟨@Fin.snoc (m+1) (fun _ => unitInterval) x (1 : I), hmem⟩]
    show gluedFun (⇑g) (⇑sig) (@Fin.snoc (m+1) (fun _ => unitInterval) x (1 : I)) = g x
    rw [gluedFun_pos _ _ (by rw [hlast]), hinit]
  have hKbd : ∀ x ∈ Cube.boundary (Fin (m+1)), ∀ t, K (x, t) = sig x := by
    intro x hx t
    have hlast : (@Fin.snoc (m+1) (fun _ => unitInterval) x t) (Fin.last (m+1)) = t :=
      Fin.snoc_last ..
    have hinit : Fin.init (@Fin.snoc (m+1) (fun _ => unitInterval) x t) = x := Fin.init_snoc ..
    have hmem : (@Fin.snoc (m+1) (fun _ => unitInterval) x t) ∈ Cube.boundary (Fin (m+2)) := by
      obtain ⟨i, hi⟩ := hx
      exact ⟨Fin.castSucc i, by rw [Fin.snoc_castSucc]; exact hi⟩
    show Ψ (@Fin.snoc (m+1) (fun _ => unitInterval) x t) = sig x
    rw [hΨΔ ⟨@Fin.snoc (m+1) (fun _ => unitInterval) x t, hmem⟩]
    show gluedFun (⇑g) (⇑sig) (@Fin.snoc (m+1) (fun _ => unitInterval) x t) = sig x
    by_cases h : t = 1
    · rw [gluedFun_pos _ _ (by rw [hlast]; exact h), hinit]
      exact hgsig x hx
    · rw [gluedFun_neg _ _ (by rw [hlast]; exact h), hinit]
  exact ⟨g, K, hK0, hKbd, fun x => (gZ x).2, hgsig, hK1⟩

end Work.ThomBordism.TwoSet
