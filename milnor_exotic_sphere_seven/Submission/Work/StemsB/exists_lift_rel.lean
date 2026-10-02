import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.exists_sq_homeomorph

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The relative homotopy lifting property of a Serre fibration

The main statement `Work.StemsB.exists_lift_rel` says that a Serre fibration `p : E → B`
(HLP with respect to all cubes `I^n`) has the *relative* homotopy lifting property for
`(I^k, ∂I^k)`, i.e. the right lifting property with respect to the inclusion

  `L_k := (∂I^k × I) ∪ (I^k × {0})  ↪  I^k × I`.

The proof (Hatcher, *Algebraic Topology*, proof of Thm 4.41) uses that the pairs
`(I^k × I, I^k × {0} ∪ ∂I^k × I)` and `(I^k × I, I^k × {0})` are homeomorphic; the
homeomorphism in question is built from the two dimensional case, which is then
"cascaded" over the coordinates of the cube.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.StemsB

noncomputable section

/-- `I^n × I`. -/
abbrev W (n : ℕ) : Type := (Fin n → I) × I

/-- `L_k`, the "cup" inside `I^k × I`: the bottom face together with the lateral boundary. -/
def LSet (k : ℕ) : Set (W k) := {q | q.2 = 0 ∨ q.1 ∈ Cube.boundary (Fin k)}

/-- Membership in the cube boundary, decomposed along the first coordinate. -/
theorem mem_boundary_succ_iff (n : ℕ) (x : Fin (n+1) → I) :
    x ∈ Cube.boundary (Fin (n+1)) ↔
      (x 0 = 0 ∨ x 0 = 1) ∨ Fin.tail x ∈ Cube.boundary (Fin n) := by
  rw [Cube.boundary, Cube.boundary]
  constructor
  · rintro ⟨i, h⟩
    induction i using Fin.cases with
    | zero => exact Or.inl h
    | succ j => exact Or.inr ⟨j, h⟩
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨0, h⟩
    · exact ⟨j.succ, hj⟩

/-- The cube boundary is closed. -/
theorem isClosed_boundary (k : ℕ) : IsClosed (Cube.boundary (Fin k)) := by
  have h : Cube.boundary (Fin k) =
      ⋃ i : Fin k, ({y : Fin k → I | y i = 0} ∪ {y : Fin k → I | y i = 1}) := by
    ext y; simp [Cube.boundary]
  rw [h]
  exact isClosed_iUnion_of_finite (fun i =>
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const))

/-- Peel the first coordinate: `I^(n+1) × I ≅ I × (I^n × I)`. -/
def peel (n : ℕ) : (W (n+1)) ≃ₜ (I × W n) where
  toFun q := (q.1 0, (Fin.tail q.1, q.2))
  invFun p := (Fin.cons p.1 p.2.1, p.2.2)
  left_inv q := by
    refine Prod.ext ?_ ?_
    · exact Fin.cons_self_tail q.1
    · rfl
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · refine Prod.ext ?_ ?_
      · simp
      · rfl
  continuous_toFun := by
    have h1 : Continuous (fun q : W (n+1) => q.1 0) := (continuous_apply 0).comp continuous_fst
    have h2 : Continuous (fun q : W (n+1) => Fin.tail q.1) :=
      continuous_pi (fun i => (continuous_apply i.succ).comp continuous_fst)
    have h3 : Continuous (fun q : W (n+1) => q.2) := continuous_snd
    exact Continuous.prodMk h1 (Continuous.prodMk h2 h3)
  continuous_invFun := by
    have h1 : Continuous (fun p : I × W n => p.1) := continuous_fst
    have h2 : Continuous (fun p : I × W n => p.2.1) := continuous_fst.comp continuous_snd
    have h3 : Continuous (fun p : I × W n => p.2.2) := continuous_snd.comp continuous_snd
    exact Continuous.prodMk (Continuous.finCons h1 h2) h3

/-- One step of the cascade: apply `Ψ` to `(a, b)` and `Φn` to the rest with the new `b`. -/
def cascadeCore (Ψ : I × I ≃ₜ I × I) (n : ℕ) (Φn : W n ≃ₜ W n) : (I × W n) ≃ₜ (I × W n) where
  toFun p := ((Ψ (p.1, p.2.2)).1, Φn (p.2.1, (Ψ (p.1, p.2.2)).2))
  invFun p := ((Ψ.symm (p.1, (Φn.symm p.2).2)).1,
    ((Φn.symm p.2).1, (Ψ.symm (p.1, (Φn.symm p.2).2)).2))
  left_inv p := by
    ext <;> simp [Homeomorph.symm_apply_apply]
  right_inv p := by
    ext <;> simp [Homeomorph.apply_symm_apply]
  continuous_toFun := by
    have h1 : Continuous (fun p : I × W n => (Ψ (p.1, p.2.2)).1) :=
      continuous_fst.comp (Ψ.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    have h2 : Continuous (fun p : I × W n => Φn (p.2.1, (Ψ (p.1, p.2.2)).2)) :=
      Φn.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
        (continuous_snd.comp (Ψ.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))))
    exact Continuous.prodMk h1 h2
  continuous_invFun := by
    have h1 : Continuous (fun p : I × W n => (Φn.symm p.2).2) :=
      continuous_snd.comp (Φn.symm.continuous.comp continuous_snd)
    have h2 : Continuous (fun p : I × W n => (Ψ.symm (p.1, (Φn.symm p.2).2)).1) :=
      continuous_fst.comp (Ψ.symm.continuous.comp (continuous_fst.prodMk h1))
    have h3 : Continuous (fun p : I × W n => (Φn.symm p.2).1) :=
      continuous_fst.comp (Φn.symm.continuous.comp continuous_snd)
    have h4 : Continuous (fun p : I × W n => (Ψ.symm (p.1, (Φn.symm p.2).2)).2) :=
      continuous_snd.comp (Ψ.symm.continuous.comp (continuous_fst.prodMk h1))
    exact Continuous.prodMk h2 (Continuous.prodMk h3 h4)

/-- The cascaded homeomorphism of `I^n × I`. -/
def cascade (Ψ : I × I ≃ₜ I × I) : (n : ℕ) → (W n ≃ₜ W n) :=
  Nat.rec (Homeomorph.refl (W 0))
    (fun n Φn => (peel n).trans ((cascadeCore Ψ n Φn).trans ((peel n).symm)))

theorem cascade_zero (Ψ : I × I ≃ₜ I × I) : cascade Ψ 0 = Homeomorph.refl (W 0) := rfl

theorem cascade_succ (Ψ : I × I ≃ₜ I × I) (n : ℕ) :
    cascade Ψ (n+1) =
      (peel n).trans ((cascadeCore Ψ n (cascade Ψ n)).trans ((peel n).symm)) := rfl

theorem cascade_succ_apply (Ψ : I × I ≃ₜ I × I) (n : ℕ) (q : W (n+1)) :
    (cascade Ψ (n+1) q).2 = (cascade Ψ n (Fin.tail q.1, (Ψ (q.1 0, q.2)).2)).2 := rfl

theorem cascade_prop (Ψ : I × I ≃ₜ I × I)
    (hΨ : ∀ p : I × I, (Ψ p).2 = 0 ↔ p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0) :
    ∀ n (q : W n), (cascade Ψ n q).2 = 0 ↔ q ∈ LSet n := by
  intro n
  induction n with
  | zero =>
    intro q
    rw [cascade_zero]
    simp only [LSet, Set.mem_ofPred_eq]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | h)
      · exact h
      · simp [Cube.boundary] at h
  | succ n ih =>
    intro q
    rw [cascade_succ_apply, ih]
    simp only [LSet, Set.mem_ofPred_eq]
    rw [mem_boundary_succ_iff, hΨ]
    tauto


/-- The cup, as a type: the subspace on which the relative lift is prescribed. -/
abbrev Cup (k : ℕ) : Type := {q : W k // q ∈ LSet k}

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-- The RLP form of `HasHLP`, adapted to the `I × Z` convention of `ContinuousMap.Homotopy`. -/
theorem hasHLP_rlp {p : C(E, B)} {Z : Type*} [TopologicalSpace Z] (hp : HasHLP p Z)
    (H : C(I × Z, B)) (f : C(Z, E)) (hf : ∀ z, H (0, z) = p (f z)) :
    ∃ G : C(I × Z, E), p.comp G = H ∧ ∀ z, G (0, z) = f z := by
  let b : C(Z, B) := H.comp ⟨fun z => (1, z), by continuity⟩
  have h1 : ∀ z, H (1, z) = b z := by intro z; rfl
  have he : ((⟨H, (by intro z; exact hf z), h1⟩ : (p.comp f).Homotopy b)).toContinuousMap = H := rfl
  obtain ⟨g, H', hH'⟩ := hp f b ⟨H, (by intro z; exact hf z), h1⟩
  refine ⟨H'.toContinuousMap, ?_, ?_⟩
  · show p.comp H'.toContinuousMap = H
    rw [hH', he]
  · intro z
    exact H'.map_zero_left z

/-- Glue the two prescribed lifts on the cup `L_k` into one continuous lift. -/
theorem exists_cup_lift (p : C(E, B)) (k : ℕ) (H : C(W k, B)) (f : C(Fin k → I, E))
    (hf : p.comp f = H.comp (zeroIncl k)) (g : C(CubeBdry k × I, E))
    (hg : p.comp g = H.comp (bdryIncl k)) (hg0 : ∀ x : CubeBdry k, g (x, 0) = f x.1) :
    ∃ k₀ : C(Cup k, E), p.comp k₀ = H.comp ⟨Subtype.val, continuous_subtype_val⟩ ∧
      (∀ q : Cup k, q.1.2 = 0 → k₀ q = f q.1.1) ∧
      (∀ (x : CubeBdry k) (t : I), k₀ ⟨(x.1, t), Or.inr x.2⟩ = g (x, t)) := by
  classical
  let Ff : Cup k → E := fun z => f z.1.1
  let Fg : Cup k → E := fun z =>
    if h : z.1.1 ∈ Cube.boundary (Fin k) then g (⟨z.1.1, h⟩, z.1.2) else f z.1.1
  let F : Cup k → E := fun z => if z.1.2 = 0 then Ff z else Fg z
  have hFf : Continuous Ff := f.continuous.comp (continuous_fst.comp continuous_subtype_val)
  have hFg : ContinuousOn Fg {z : Cup k | z.1.1 ∈ Cube.boundary (Fin k)} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Set.domRestrict {z : Cup k | z.1.1 ∈ Cube.boundary (Fin k)} Fg) =
        (fun z : {z : Cup k // z.1.1 ∈ Cube.boundary (Fin k)} =>
          g ((⟨z.1.1.1, z.2⟩ : CubeBdry k), z.1.1.2)) := by
      funext z
      rw [Set.domRestrict_apply]
      simp only [Fg]
      split_ifs with h
      · rfl
      · exact absurd z.2 h
    rw [heq]
    fun_prop
  have hcl : closure {z : Cup k | ¬ (z.1.2 = 0)} ⊆ {z : Cup k | z.1.1 ∈ Cube.boundary (Fin k)} := by
    apply closure_minimal
    · intro z hz
      rcases z.2 with h | h
      · exact absurd h hz
      · exact h
    · exact (isClosed_boundary k).preimage (continuous_fst.comp continuous_subtype_val)
  have hF : Continuous F := by
    have hsc : IsClosed {z : Cup k | z.1.2 = 0} :=
      isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const
    refine continuous_if ?_ (hFf.continuousOn) (hFg.mono hcl)
    · intro z hz
      have hz0 : z.1.2 = 0 := by
        have h2 := hz.1
        rw [IsClosed.closure_eq hsc] at h2
        exact h2
      show Ff z = Fg z
      by_cases h : z.1.1 ∈ Cube.boundary (Fin k)
      · simp only [Ff, Fg, dif_pos h]
        rw [hz0, hg0]
      · simp only [Ff, Fg, dif_neg h]
  refine ⟨⟨F, hF⟩, ?_, ?_, ?_⟩
  · ext z
    show p (F z) = H z.1
    by_cases hz : z.1.2 = 0
    · have h1 : F z = f z.1.1 := by simp only [F, hz, ↓reduceIte, Ff]
      rw [h1]
      show (p.comp f) z.1.1 = H z.1
      rw [DFunLike.congr_fun hf z.1.1]
      show H (z.1.1, (0 : I)) = H z.1
      rw [show (z.1.1, (0 : I)) = z.1 from Prod.ext rfl hz.symm]
    · have hz' : z.1.1 ∈ Cube.boundary (Fin k) := z.2.resolve_left hz
      have h1 : F z = g (⟨z.1.1, hz'⟩, z.1.2) := by
        simp only [F, hz, ↓reduceIte, Fg, dif_pos hz']
      rw [h1]
      show (p.comp g) (⟨z.1.1, hz'⟩, z.1.2) = H z.1
      rw [DFunLike.congr_fun hg (⟨z.1.1, hz'⟩, z.1.2)]
      rfl
  · intro q hq
    show F q = f q.1.1
    simp only [F, hq, ↓reduceIte, Ff]
  · intro x t
    by_cases ht : t = 0
    · subst ht
      show F (⟨(x.1, 0), Or.inr x.2⟩ : Cup k) = g (x, 0)
      have h1 : F (⟨(x.1, 0), Or.inr x.2⟩ : Cup k) = f x.1 := by
        simp only [F, ↓reduceIte, Ff]
      rw [h1, hg0]
    · show F (⟨(x.1, t), Or.inr x.2⟩ : Cup k) = g (x, t)
      have h1 : F (⟨(x.1, t), Or.inr x.2⟩ : Cup k) = g (x, t) := by
        simp only [F, ht, ↓reduceIte, Fg, dif_pos x.2]
      exact h1

/-- The cube homeomorphism: `L_n` is carried to the bottom face. -/
theorem exists_cube_homeomorph' (Ψ : I × I ≃ₜ I × I)
    (hΨ : ∀ p : I × I, (Ψ p).2 = 0 ↔ p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0) (n : ℕ) :
    ∃ Φ : W n ≃ₜ W n, ∀ q : W n, (Φ q).2 = 0 ↔ q ∈ LSet n :=
  ⟨cascade Ψ n, cascade_prop Ψ hΨ n⟩

/-- Transport of the absolute homotopy lifting property along a homeomorphism of the ambient
space which identifies the cup `L_k` with the bottom face. -/
theorem hasHLPRel_of_homeomorph' (p : C(E, B)) (k : ℕ) (Φ : W k ≃ₜ W k)
    (hΦ : ∀ q : W k, (Φ q).2 = 0 ↔ q ∈ LSet k)
    (hp : HasHLP p (Fin k → I)) : HasHLPRel p k := by
  intro H f hf g hg hg0
  obtain ⟨k₀, hk₀, hk₀bot, hk₀lat⟩ := exists_cup_lift p k H f hf g hg hg0
  let Θ : I × (Fin k → I) ≃ₜ W k := Homeomorph.prodComm I (Fin k → I)
  let H₂ : C(I × (Fin k → I), B) :=
    H.comp ((⟨Φ.symm, Φ.symm.continuous⟩ : C(W k, W k)).comp
      (⟨Θ, Θ.continuous⟩ : C(I × (Fin k → I), W k)))
  have hΘ : ∀ (q : W k), Θ.symm q = (q.2, q.1) := fun q => rfl
  have hΨmem : ∀ x : Fin k → I, Φ.symm (x, 0) ∈ LSet k := by
    intro x
    exact (hΦ (Φ.symm (x, 0))).mp (by rw [Homeomorph.apply_symm_apply])
  let f₂fun : (Fin k → I) → E := fun x => k₀ ⟨Φ.symm (x, 0), hΨmem x⟩
  have f₂cont : Continuous f₂fun :=
    k₀.continuous.comp (Continuous.subtype_mk
      ((Φ.symm.continuous).comp (by continuity : Continuous fun x : Fin k → I => (x, (0 : I))))
      (fun x => hΨmem x))
  let f₂ : C(Fin k → I, E) := ⟨f₂fun, f₂cont⟩
  have hf₂ : ∀ x, H₂ (0, x) = p (f₂ x) := by
    intro x
    change H (Φ.symm (Θ (0, x))) = p (k₀ ⟨Φ.symm (x, 0), hΨmem x⟩)
    rw [show Θ (0, x) = (x, 0) from rfl]
    show (H.comp ⟨Subtype.val, continuous_subtype_val⟩) ⟨Φ.symm (x, 0), hΨmem x⟩ =
      p (k₀ ⟨Φ.symm (x, 0), hΨmem x⟩)
    rw [← hk₀]
    rfl
  obtain ⟨G₂, hG₂, hG₂0⟩ := hasHLP_rlp hp H₂ f₂ hf₂
  refine ⟨G₂.comp ⟨Φ.trans Θ.symm, (Φ.trans Θ.symm).continuous⟩, ?_, ?_, ?_⟩
  · ext q
    show p (G₂ ((Φ.trans Θ.symm) q)) = H q
    rw [show (Φ.trans Θ.symm) q = Θ.symm (Φ q) from rfl]
    show (p.comp G₂) (Θ.symm (Φ q)) = H q
    rw [hG₂]
    change H (Φ.symm (Θ (Θ.symm (Φ q)))) = H q
    rw [Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]
  · intro x
    have hmem : (x, 0) ∈ LSet k := Or.inl rfl
    have h0 : (Φ (x, 0)).2 = 0 := (hΦ (x, 0)).mpr hmem
    show G₂ ((Φ.trans Θ.symm) (x, 0)) = f x
    rw [show (Φ.trans Θ.symm) (x, 0) = Θ.symm (Φ (x, 0)) from rfl]
    rw [show Θ.symm (Φ (x, 0)) = (0, (Φ (x, 0)).1) from by rw [hΘ]; exact Prod.ext h0 rfl]
    rw [hG₂0]
    show k₀ ⟨Φ.symm (((Φ (x, 0)).1), (0 : I)), hΨmem _⟩ = f x
    have harg : (⟨Φ.symm ((Φ (x, 0)).1, 0), hΨmem _⟩ : Cup k) = ⟨(x, 0), hmem⟩ := by
      apply Subtype.ext
      show Φ.symm ((Φ (x, 0)).1, 0) = (x, 0)
      rw [show ((Φ (x, 0)).1, (0 : I)) = Φ (x, 0) from Prod.ext rfl h0.symm]
      exact Homeomorph.symm_apply_apply Φ (x, 0)
    rw [harg]
    exact hk₀bot ⟨(x, 0), hmem⟩ rfl
  · intro x t
    have hmem : (x.1, t) ∈ LSet k := Or.inr x.2
    have h0 : (Φ (x.1, t)).2 = 0 := (hΦ (x.1, t)).mpr hmem
    show G₂ ((Φ.trans Θ.symm) (x.1, t)) = g (x, t)
    rw [show (Φ.trans Θ.symm) (x.1, t) = Θ.symm (Φ (x.1, t)) from rfl]
    rw [show Θ.symm (Φ (x.1, t)) = (0, (Φ (x.1, t)).1) from by rw [hΘ]; exact Prod.ext h0 rfl]
    rw [hG₂0]
    show k₀ ⟨Φ.symm (((Φ (x.1, t)).1), (0 : I)), hΨmem _⟩ = g (x, t)
    have harg : (⟨Φ.symm ((Φ (x.1, t)).1, 0), hΨmem _⟩ : Cup k) = ⟨(x.1, t), hmem⟩ := by
      apply Subtype.ext
      show Φ.symm ((Φ (x.1, t)).1, 0) = (x.1, t)
      rw [show ((Φ (x.1, t)).1, (0 : I)) = Φ (x.1, t) from Prod.ext rfl h0.symm]
      exact Homeomorph.symm_apply_apply Φ (x.1, t)
    rw [harg]
    exact hk₀lat x t

/-- **The relative homotopy lifting property of a Serre fibration.** -/
theorem exists_lift_rel {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : IsSerreFibration p) (k : ℕ) : HasHLPRel p k := by
  obtain ⟨Ψ, hΨ⟩ := exists_sq_homeomorph
  obtain ⟨Φ, hΦ⟩ := exists_cube_homeomorph' Ψ hΨ k
  exact hasHLPRel_of_homeomorph' p k Φ hΦ (hp k)

end

end Work.StemsB
