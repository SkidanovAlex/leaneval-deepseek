import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Basic
import Submission.Work.RatHurewicz.Cofibre.compressRel_cofibre_range
import Submission.Work.RatHurewicz.Cofibre.URetractEqv
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.basepoint_transport

/-!
# `π_k` of the collapse of the cofibre of a fibration

The main theorem is `Work.RatHurewicz.Cofibre.piMap_cofibreCollapse_bijective`.  The route is the
long exact sequence chase described in its docstring; the geometric input is the compression
property of the cofibre of an `n`-connected inclusion
(`Work.RatHurewicz.Cofibre.compressRel_cofibre_range`), and the two exact-sequence inputs are
`Work.StemsB.FibrationLES` (for `π_k(p)`) and `Work.Serre.surjective_pimap_setIncl_of_compressRel`
(compression in dimension `k` gives the surjectivity of the inclusion on `π_k`).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz.Cofibre

open Work.StemsB

noncomputable section

/-! ## Transfer of the triviality of `π_j` to all base points -/

/-- For a path connected space `X`, the triviality of `π_j(X, x)` for `j ≤ n` at one base point
implies the triviality at every base point. -/
theorem subsingleton_homotopyGroup_of_pathConnected {X : Type} [TopologicalSpace X] (x : X)
    (hpc : PathConnectedSpace X) (n : ℕ)
    (h : ∀ j : ℕ, j ≤ n → Subsingleton (HomotopyGroup (Fin j) X x)) :
    ∀ (j : ℕ), j ≤ n → ∀ (y : X), Subsingleton (HomotopyGroup (Fin j) X y) := by
  intro j hj y
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    haveI := h 0 (by omega)
    have hZ : Subsingleton (ZerothHomotopy X) :=
      ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm.injective
        (Subsingleton.elim _ _)⟩
    exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := y)).injective
      (hZ.elim _ _)⟩
  · obtain ⟨n', rfl⟩ : ∃ n', j = n' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨e⟩ := Work.StemsB.basepoint_transport n' (Nonempty.some (hpc.joined y x))
    haveI := h (n' + 1) hj
    exact ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩

/-! ## Surjectivity of `π_j(f)` from the compression of `(X, range f)` -/

/-- **Compression in dimension `j+1` makes `π_{j+1}(f)` surjective**, for a map `f : C(A,X)` with a
continuous *section* `S` of the range parametrisation.

Given a based cube `g : (I^{j+1}, ∂I^{j+1}) → (X, f a₀)`, compression provides a homotopy relative
to `∂I^{j+1}` from `g` to a cube `G₁` with values in `range f`; composing `G₁` with the section `S`
gives a based cube of `A` (the boundary condition uses `S (f a₀) = a₀`) whose image under `f` is
`f ∘ S ∘ G₁ = G₁`, homotopic to `g`. -/
theorem surjective_pimap_of_compressRel_range {A X : Type} [TopologicalSpace A]
    [TopologicalSpace X] (f : C(A, X)) (a₀ : A) (n : ℕ)
    (h : ∀ d, d ≤ n → CompressRel X (Set.range ⇑f) d)
    (S : C(↥(Set.range ⇑f), A)) (hS : ∀ b, f (S b) = b.1)
    (hS₀ : S ⟨f a₀, ⟨a₀, rfl⟩⟩ = a₀) (j : ℕ) (hj : j + 1 ≤ n) :
    Function.Surjective (πmap f j a₀) := by
  intro y
  induction y using Quotient.inductionOn with
  | h g =>
    have hbdf : ∀ x, x ∈ Cube.boundary (Fin (j + 1)) → g.1 x ∈ Set.range ⇑f := by
      intro x hx
      rw [g.2 x hx]
      exact ⟨a₀, rfl⟩
    obtain ⟨G, hG0, hGb, hG1⟩ := h (j + 1) hj g.1 hbdf
    let g' : Ω^ (Fin (j + 1)) A a₀ :=
      ⟨⟨fun x => S ⟨G (x, 1), hG1 x⟩, by fun_prop⟩, by
        intro x hx
        show S ⟨G (x, 1), hG1 x⟩ = a₀
        have hx1 : G (x, 1) = f a₀ := by rw [hGb x hx 1]; exact g.2 x hx
        have hxe : (⟨G (x, 1), hG1 x⟩ : ↥(Set.range ⇑f)) = ⟨f a₀, ⟨a₀, rfl⟩⟩ := Subtype.ext hx1
        rw [hxe, hS₀]⟩
    refine ⟨⟦g'⟧, ?_⟩
    rw [πmap_apply_mk]
    apply Quotient.sound
    have hhom : (g.1).HomotopicRel ((genLoopMap f (j + 1) g').1)
        (Cube.boundary (Fin (j + 1))) := by
      refine ⟨{ toHomotopy := { toFun := fun p => G (p.2, p.1), continuous_toFun := ?_, map_zero_left := ?_, map_one_left := ?_ }, prop' := ?_ }⟩
      · fun_prop
      · intro x
        show G (x, 0) = g.1 x
        exact hG0 x
      · intro x
        show G (x, 1) = f (g' x)
        exact (hS ⟨G (x, 1), hG1 x⟩).symm
      · intro t x hx
        show G (x, t) = g.1 x
        exact hGb x hx t
    exact hhom.symm

/-! ## The main theorem -/

/-- **`π_k` of the collapse of the cofibre, at the base point induced by `x ∈ E`.**  For a
Hurewicz fibration `p : E → B` and a point `x : E` whose fibre `F = p ⁻¹' {p x}` is
`k`-connected (`k ≥ 2`), the collapse `c := cofibreCollapse (setIncl F) p (p x) _ : E ∪_F CF → B`
of the cofibre of `F ↪ E` is *bijective* on `π_k` at the base point
`cofibreIncl (setIncl F) x` of the cofibre.

Route (a pure long-exact-sequence chase, no Blakers–Massey).

Write `C := cofibre (setIncl F)` and `A := cofibreInclCone ι '' univ ⊆ C` (the image of the cone).

* `π_k(p) : π_k(E) → π_k(B)` is bijective: exactness at `π_k(E)` of the fibration sequence
  (`π_k(F) = 0`) gives injectivity, and exactness at `π_k(B)` together with `π_{k-1}(F) = 0` gives
  surjectivity.
* `c ∘ cofibreIncl = p`, so `π_k(p) = π_k(c) ∘ π_k(incl)`; hence `π_k(c)` is surjective and
  `π_k(incl)` is injective.
* `π_k(incl)` is surjective: the pair `(C, range incl)` is compressed in dimension `k`
  (`compressRel_cofibre_range`, from the `k`-connectivity of `F`), and compression in dimension `k`
  transfers to surjectivity of `π_k` of the inclusion (`surjective_pimap_of_compressRel_range`,
  using the retraction `cofibreURetract` of the half-open cone as the section).
* Hence `π_k(c)`: given `y` with `π_k(c) y = 1`, write `y = π_k(incl) e`, then `π_k(p) e = 1`, so
  `e = 1` and `y = 1`. -/
theorem piMap_cofibreCollapse_bijective {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (k : ℕ) (hk : 2 ≤ k) (x : E)
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p x})) ⟨x, rfl⟩)) :
    Function.Bijective (Work.Serre.piMapN (Work.RatHurewicz.cofibreCollapse
      (Work.RatHurewicz.setIncl (p ⁻¹' {p x})) p (p x) (fun y => y.2)) k
      (Work.RatHurewicz.cofibreIncl (Work.RatHurewicz.setIncl (p ⁻¹' {p x})) x)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  haveI : Nonempty ↥(p ⁻¹' {p x}) := ⟨⟨x, rfl⟩⟩
  haveI : Nonempty E := ⟨x⟩
  have hpiMapN : Work.Serre.piMapN (Work.RatHurewicz.cofibreCollapse
      (Work.RatHurewicz.setIncl (p ⁻¹' {p x})) p (p x) (fun y => y.2)) (m + 2)
        (Work.RatHurewicz.cofibreIncl (Work.RatHurewicz.setIncl (p ⁻¹' {p x})) x)
      = ⇑(πmap (Work.RatHurewicz.cofibreCollapse
          (Work.RatHurewicz.setIncl (p ⁻¹' {p x})) p (p x) (fun y => y.2)) (m + 1)
          (Work.RatHurewicz.cofibreIncl (Work.RatHurewicz.setIncl (p ⁻¹' {p x})) x)) := by
    funext a
    induction a using Quotient.inductionOn with
    | h γ => rfl
  rw [hpiMapN]
  set ι : C(↥(p ⁻¹' {p x}), E) := Work.RatHurewicz.setIncl (p ⁻¹' {p x}) with hι
  set incl : C(E, Work.RatHurewicz.cofibre ι) := Work.RatHurewicz.cofibreIncl ι with hincl
  set c : C(Work.RatHurewicz.cofibre ι, B) :=
    Work.RatHurewicz.cofibreCollapse ι p (p x) (fun y => y.2) with hc
  -- the base point of the cofibre
  have hp_incl : ∀ e : E, c (incl e) = p e := by
    intro e
    exact Work.RatHurewicz.cofibreCollapse_incl ι p (p x) (fun y => y.2) e
  -- (1) `π_k(p)` is bijective
  have hpbij : Function.Bijective (πmap p (m+1) x) := by
    obtain ⟨d, h1, h2, -⟩ := Work.StemsB.fibrationLES_of_isHurewiczFibration p hp x m
    have hsub2 : Subsingleton (HomotopyGroup (Fin (m+2)) (Work.StemsB.fibre p (p x))
        (Work.StemsB.fibrePoint p x)) := hconn (m+2) (by omega)
    have hsub1 : Subsingleton (HomotopyGroup (Fin (m+1)) (Work.StemsB.fibre p (p x))
        (Work.StemsB.fibrePoint p x)) := hconn (m+1) (by omega)
    constructor
    · intro a b hab
      haveI := hsub2
      have hker : πmap p (m+1) x (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, hab, mul_inv_cancel]
      obtain ⟨w, hw⟩ := (h1 (a * b⁻¹)).mp hker
      have hw1 : w = 1 := Subsingleton.elim w 1
      have hab1 : a * b⁻¹ = 1 := by
        rw [← hw, hw1]
        exact map_one _
      exact mul_inv_eq_one.mp hab1
    · intro y
      haveI := hsub1
      have hd : d y = 1 := Subsingleton.elim (d y) 1
      obtain ⟨e, he⟩ := (h2 y).mp hd
      exact ⟨e, he⟩
  -- (2) the factorisation `π_k(p) = π_k(c) ∘ π_k(incl)`
  have hfac : ∀ a : HomotopyGroup (Fin (m+2)) E x,
      πmap c (m+1) (incl x) (πmap incl (m+1) x a) = πmap p (m+1) x a := by
    intro a
    induction a using Quotient.inductionOn with
    | h γ =>
      rw [πmap_apply_mk, πmap_apply_mk, πmap_apply_mk]
      apply Quotient.sound
      have h : genLoopMap c (m+2) (genLoopMap incl (m+2) γ) = genLoopMap p (m+2) γ := by
        ext t
        exact hp_incl (γ t)
      rw [h]
      exact GenLoop.Homotopic.refl _
  -- (3) `π_k(incl)` is surjective, from the compression of `(C, range incl)`
  have hFconn : ∀ (j : ℕ), j ≤ m + 1 → ∀ y : ↥(p ⁻¹' {p x}),
      Subsingleton (HomotopyGroup (Fin j) ↥(p ⁻¹' {p x}) y) := by
    haveI h0 : Subsingleton (HomotopyGroup (Fin 0) ↥(p ⁻¹' {p x}) ⟨x, rfl⟩) :=
      hconn 0 (by omega)
    have hZ : Subsingleton (ZerothHomotopy ↥(p ⁻¹' {p x})) :=
      ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x := ⟨x, rfl⟩)).symm.injective
        (Subsingleton.elim _ _)⟩
    have hpc : PathConnectedSpace ↥(p ⁻¹' {p x}) :=
      pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk ⟨x, rfl⟩⟩, hZ⟩
    exact fun j hj y => subsingleton_homotopyGroup_of_pathConnected ⟨x, rfl⟩ hpc (m+1)
      (fun j hj => hconn j (by omega)) j hj y
  have hcompress : ∀ d, d ≤ m + 2 → CompressRel (Work.RatHurewicz.cofibre ι)
      (Set.range ⇑incl) d :=
    compressRel_cofibre_range ι (m+1) hFconn
  -- the section of the range parametrisation, given by the retraction of the half-open cone
  have hmemU : ∀ a : ↥(Set.range ⇑incl), a.1 ∈ Work.RatHurewicz.cofibreU ι := by
    rintro ⟨z, ⟨e, rfl⟩⟩
    exact Work.RatHurewicz.cofibreIncl_mem_cofibreU ι e
  let ψ : C(↥(Set.range ⇑incl), E) :=
    ⟨fun a => Work.RatHurewicz.cofibreURetract ι x ⟨a.1, hmemU a⟩, by
      refine (Work.RatHurewicz.cofibreURetract ι x).continuous.comp ?_
      exact Continuous.subtype_mk continuous_subtype_val _⟩
  have hψ_comp : ∀ e : E, Work.RatHurewicz.cofibreURetract ι x
      ⟨incl e, hmemU ⟨incl e, ⟨e, rfl⟩⟩⟩ = e := by
    intro e
    have h := congrFun (congrArg (fun k : C(E, E) => ⇑k)
      (Work.RatHurewicz.cofibreURetract_comp_cofibreUIncl ι x)) e
    have h' : Work.RatHurewicz.cofibreURetract ι x (Work.RatHurewicz.cofibreUIncl ι e) = e := h
    rw [show Work.RatHurewicz.cofibreUIncl ι e
      = (⟨incl e, hmemU ⟨incl e, ⟨e, rfl⟩⟩⟩ : ↥(Work.RatHurewicz.cofibreU ι)) from rfl] at h'
    exact h'
  have hψS : ∀ b : ↥(Set.range ⇑incl), incl (ψ b) = b.1 := by
    rintro ⟨z, ⟨e, rfl⟩⟩
    show incl (Work.RatHurewicz.cofibreURetract ι x ⟨incl e, hmemU ⟨incl e, ⟨e, rfl⟩⟩⟩) = incl e
    rw [hψ_comp e]
  have hψS₀ : ψ ⟨incl x, ⟨x, rfl⟩⟩ = x := by
    show Work.RatHurewicz.cofibreURetract ι x ⟨incl x, hmemU ⟨incl x, ⟨x, rfl⟩⟩⟩ = x
    exact hψ_comp x
  have hincl : Function.Surjective (πmap incl (m+1) x) :=
    surjective_pimap_of_compressRel_range incl x (m+2) hcompress ψ hψS hψS₀ (m+1) (by omega)
  -- (4) the assembly
  constructor
  · intro a b hab
    obtain ⟨e, he⟩ := hincl a
    obtain ⟨f', hf'⟩ := hincl b
    rw [← he, ← hf', hfac e, hfac f'] at hab
    have hef : e = f' := hpbij.1 hab
    rw [← he, ← hf', hef]
  · intro y
    obtain ⟨e, he⟩ := hpbij.2 y
    exact ⟨πmap incl (m+1) x e, by rw [hfac e, he]⟩

end

end Work.RatHurewicz.Cofibre
