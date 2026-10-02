import Submission.Work.Stems.Pinch.swapHom
import Submission.Work.RatHurewicz.GluingPinch.ReadSign

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sign of a coordinate-permutation reading of a based cube

`Work.Stems.readingPerm`: composing a based `n`-cube with the coordinate permutation `π` multiplies
its class by `sign π`:

> `cl (p ∘ permMap π) = (cl p) ^ (sign π)`.

This is the `sign`-factor of the arrangement ("shrink / move / expand") computation of the general
homotopy-addition theorem: the layout reads the pieces through *coordinatewise* charts
(`Work.RatHurewicz.GluingPinch.readingCoordwise`, proved) possibly composed with a permutation, and
the signs multiply.

The proof is the induction `Equiv.Perm.swap_induction_on`: for a transposition `Equiv.swap i j` the
permutation reading is homotopic, *through maps of the pair `(I^n, ∂I^n)`*, to the reversal of one
coordinate (`Work.Stems.swapHom`, the sibling file — the explicit rotation witness), whose class is
the inverse (`Work.RatHurewicz.revCube_class`); and `Equiv.Perm.sign` is multiplicative.

(NB: `σ` is notation for `unitInterval.symm` in this workspace, so it cannot be used as a binder
name.)
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems

noncomputable section

/-- The coordinate permutation of the cube: `(permMap π u) j = u (π j)`. -/
def permMap {n : ℕ} (pi : Equiv.Perm (Fin n)) : C(IC n, IC n) :=
  ⟨fun u j => u (pi j), continuous_pi fun j => continuous_apply (pi j)⟩

@[simp] theorem permMap_apply {n : ℕ} (pi : Equiv.Perm (Fin n)) (u : IC n) (j : Fin n) :
    permMap pi u j = u (pi j) := rfl

theorem permMap_one {n : ℕ} : permMap (1 : Equiv.Perm (Fin n)) = ContinuousMap.id (IC n) := by
  ext u j
  rw [permMap_apply, Equiv.Perm.one_apply]
  rfl

theorem permMap_mul {n : ℕ} (pi tau : Equiv.Perm (Fin n)) :
    permMap (tau * pi) = (permMap pi).comp (permMap tau) := by
  ext u j
  simp only [permMap_apply, Equiv.Perm.mul_apply, ContinuousMap.comp_apply]

/-- The reversal of the coordinate `i` of the cube. -/
def flipMap {n : ℕ} (i : Fin n) : C(IC n, IC n) :=
  ⟨fun u j => if j = i then unitInterval.symm (u j) else u j,
   continuous_pi fun j => by
     by_cases hj : j = i
     · have hfun : (fun u : IC n => (if j = i then unitInterval.symm (u j) else u j))
           = fun u : IC n => unitInterval.symm (u j) := by
         funext u; rw [if_pos hj]
       rw [hfun]
       exact unitInterval.continuous_symm.comp (continuous_apply j)
     · have hfun : (fun u : IC n => (if j = i then unitInterval.symm (u j) else u j))
           = fun u : IC n => u j := by
         funext u; rw [if_neg hj]
       rw [hfun]
       exact continuous_apply j⟩

@[simp] theorem flipMap_apply {n : ℕ} (i : Fin n) (u : IC n) (j : Fin n) :
    flipMap i u j = if j = i then unitInterval.symm (u j) else u j := rfl

theorem permMap_boundary {n : ℕ} (pi : Equiv.Perm (Fin n)) {u : IC n}
    (hu : u ∈ Cube.boundary (Fin n)) : permMap pi u ∈ Cube.boundary (Fin n) := by
  obtain ⟨k, hk⟩ := hu
  exact ⟨pi.symm k, by rw [permMap_apply, Equiv.apply_symm_apply]; exact hk⟩

theorem flipMap_boundary {n : ℕ} (i : Fin n) {u : IC n}
    (hu : u ∈ Cube.boundary (Fin n)) : flipMap i u ∈ Cube.boundary (Fin n) := by
  obtain ⟨k, hk⟩ := hu
  refine ⟨k, ?_⟩
  rw [flipMap_apply]
  by_cases hk' : k = i
  · rw [if_pos hk']
    rcases hk with hk | hk
    · right
      apply Subtype.ext
      show (1:ℝ) - ((u k : unitInterval) : ℝ) = 1
      rw [hk]; norm_num
    · left
      apply Subtype.ext
      show (1:ℝ) - ((u k : unitInterval) : ℝ) = 0
      rw [hk]; norm_num
  · rw [if_neg hk']
    exact hk

theorem flipMap_eq_coordUpd {n : ℕ} (i : Fin n) :
    flipMap i = Work.RatHurewicz.coordUpd n i Work.RatHurewicz.revC := by
  ext u j
  rw [flipMap_apply, Work.RatHurewicz.coordUpd_apply, Function.update_apply]
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj, hj]
    rfl
  · rw [if_neg hj, if_neg hj]

/-- **The squeeze lemma**: a homotopy of self-maps of `I^n`, each slice of which carries `∂I^n` into
`∂I^n`, gives the same class for `p ∘ φ` and `p ∘ ψ`. -/
theorem cl_compMap_eq {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (φ ψ : C(IC n, IC n)) (H : C(IC n × unitInterval, IC n))
    (h0 : ∀ u, H (u, 0) = φ u) (h1 : ∀ u, H (u, 1) = ψ u)
    (hφ : ∀ u ∈ Cube.boundary (Fin n), φ u ∈ Cube.boundary (Fin n))
    (hψ : ∀ u ∈ Cube.boundary (Fin n), ψ u ∈ Cube.boundary (Fin n))
    (Hb : ∀ u ∈ Cube.boundary (Fin n), ∀ t, H (u, t) ∈ Cube.boundary (Fin n))
    (p : GenLoop (Fin n) X x₀) :
    Work.RatHurewicz.cl n X x₀ ⟨p.1.comp φ, fun u hu => p.2 _ (hφ u hu)⟩ =
      Work.RatHurewicz.cl n X x₀ ⟨p.1.comp ψ, fun u hu => p.2 _ (hψ u hu)⟩ := by
  refine Quotient.sound ⟨⟨⟨fun z : unitInterval × IC n => p.1 (H (z.2, z.1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact p.1.continuous.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst))
  · intro u
    show p.1 (H (u, 0)) = p.1 (φ u)
    rw [h0]
  · intro u
    show p.1 (H (u, 1)) = p.1 (ψ u)
    rw [h1]
  · intro t u hu
    show p.1 (H (u, t)) = p.1 (φ u)
    rw [p.2 (H (u, t)) (Hb u hu t), p.2 (φ u) (hφ u hu)]

/-- The reversal of a coordinate inverts the class. -/
theorem flipMap_class {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (i : Fin n) (p : GenLoop (Fin n) X x₀) :
    Work.RatHurewicz.cl n X x₀ ⟨p.1.comp (flipMap i), fun u hu => p.2 _ (flipMap_boundary i hu)⟩
      = (Work.RatHurewicz.cl n X x₀ p)⁻¹ := by
  have heq : (⟨p.1.comp (flipMap i), fun u hu => p.2 _ (flipMap_boundary i hu)⟩ :
      GenLoop (Fin n) X x₀) = Work.RatHurewicz.revCube i p := by
    refine Subtype.ext ?_
    show p.1.comp (flipMap i) = p.1.comp (Work.RatHurewicz.coordUpd n i Work.RatHurewicz.revC)
    rw [flipMap_eq_coordUpd]
  rw [heq, Work.RatHurewicz.revCube_class]

/-- **A transposition of coordinates inverts the class.** -/
theorem permMap_swap_class {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    {i j : Fin n} (hij : i ≠ j) (p : GenLoop (Fin n) X x₀) :
    Work.RatHurewicz.cl n X x₀
        ⟨p.1.comp (permMap (Equiv.swap i j)), fun u hu => p.2 _ (permMap_boundary _ hu)⟩
      = (Work.RatHurewicz.cl n X x₀ p)⁻¹ := by
  obtain ⟨H, h0, h1, Hb⟩ := swapHom i j hij
  have hstep := cl_compMap_eq (flipMap i) (permMap (Equiv.swap i j)) H h0 h1
    (fun u hu => flipMap_boundary i hu)
    (fun u hu => permMap_boundary (Equiv.swap i j) hu) Hb p
  rw [← hstep]
  exact flipMap_class i p

/-- **The sign of a coordinate-permutation reading.** -/
theorem readingPerm_aux {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (pi : Equiv.Perm (Fin n)) (p : GenLoop (Fin n) X x₀) :
    Work.RatHurewicz.cl n X x₀
        ⟨p.1.comp (permMap pi), fun u hu => p.2 _ (permMap_boundary pi hu)⟩
      = (Work.RatHurewicz.cl n X x₀ p) ^ (((Equiv.Perm.sign pi : ℤˣ) : ℤ)) := by
  classical
  revert p
  induction pi using Equiv.Perm.swap_induction_on with
  | one =>
      intro p
      have hsign : ((Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) = 1 := by
        rw [Equiv.Perm.sign_one]; rfl
      have heq : (⟨p.1.comp (permMap 1), fun u hu => p.2 _ (permMap_boundary 1 hu)⟩ :
          GenLoop (Fin n) X x₀) = p := by
        refine Subtype.ext ?_
        show p.1.comp (permMap 1) = p.1
        rw [permMap_one, ContinuousMap.comp_id]
      rw [heq, hsign, zpow_one]
  | swap_mul f x y hxy ih =>
      intro p
      have hsign : ((Equiv.Perm.sign (Equiv.swap x y * f) : ℤˣ) : ℤ)
          = -(((Equiv.Perm.sign f : ℤˣ) : ℤ)) := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
        simp
      rw [hsign]
      set q : GenLoop (Fin n) X x₀ :=
        ⟨p.1.comp (permMap f), fun u hu => p.2 _ (permMap_boundary f hu)⟩ with hq
      have heq : (⟨p.1.comp (permMap (Equiv.swap x y * f)),
            fun u hu => p.2 _ (permMap_boundary (Equiv.swap x y * f) hu)⟩ :
          GenLoop (Fin n) X x₀)
          = ⟨q.1.comp (permMap (Equiv.swap x y)),
              fun u hu => q.2 _ (permMap_boundary (Equiv.swap x y) hu)⟩ := by
        have hv : p.1.comp (permMap (Equiv.swap x y * f))
            = q.1.comp (permMap (Equiv.swap x y)) := by
          rw [permMap_mul, ContinuousMap.comp_assoc]
        exact Subtype.ext hv
      rw [heq]
      rw [permMap_swap_class hxy q, hq, ih p]
      rw [← zpow_neg]

/-- **The sign of a coordinate-permutation reading of a based cube** (the form requested by the
layout computation). -/
theorem readingPerm {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (pi : Equiv.Perm (Fin n)) (p q : GenLoop (Fin n) X x₀)
    (hq : ∀ u : IC n, q.1 u = p.1 (fun j => u (pi.symm j))) :
    Work.RatHurewicz.cl n X x₀ q
      = (Work.RatHurewicz.cl n X x₀ p) ^ (((Equiv.Perm.sign pi : ℤˣ) : ℤ)) := by
  have heq : q = ⟨p.1.comp (permMap pi.symm), fun u hu => p.2 _ (permMap_boundary pi.symm hu)⟩ := by
    refine Subtype.ext (ContinuousMap.ext fun u => ?_)
    rw [hq u]
    show p.1 (fun j => u (pi.symm j)) = p.1 (fun j => u (pi.symm j))
    rfl
  rw [heq, readingPerm_aux pi.symm p, Equiv.Perm.sign_symm]

end

end Work.Stems
