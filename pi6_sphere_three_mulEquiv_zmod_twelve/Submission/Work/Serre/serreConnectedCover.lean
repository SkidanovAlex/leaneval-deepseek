import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.StemsB.LESExact
import Submission.Work.Serre.piOneHomotopyFibreSubsingleton
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre

/-!
# Serre's connected cover: the homotopy fibre of a Postnikov-type map

For `g : C(Y, P)` with `π_i(g)` bijective for `i ≤ m` and `π_i(P) = 0` for `m < i ≤ N`, the homotopy
fibre `F = homotopyFibre g y₀` is `m`-connected and the projection `F → Y` is a `π_i`-isomorphism for
`m < i < N`.

The proof is the long exact sequence of the pair `(P, Y)` (`Work.RatHurewicz.pair_les`) together
with the three low-degree facts

* `π₀(F) = 0` — `Work.Serre.pathConnectedSpace_homotopyFibre` plus `π₀`-injectivity and
  `π₁`-surjectivity of `g`;
* `π₁(F) = 0` — `Work.Serre.piOneHomotopyFibreSubsingleton` (when `m = 1`, so `π₂(P) = 0`) or
  `Work.Serre.piOneHomotopyFibreSubsingleton_of_surjective` (when `m ≥ 2`, so `π₂(g)` is onto);
* exactness at `π₂(Y)` — the `k = 0` case of the pair sequence, proved directly from
  `Work.StemsB.les_exact_B` and `Work.RatHurewicz.fibreDMap_eq_pairShiftHom`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

variable {Y P : Type} [TopologicalSpace Y] [TopologicalSpace P]

/-! ## `π₀`-injectivity in geometric form -/

/-- The `0`-cube of `X` at `x₀` with value `a` (the boundary of the `0`-cube is empty, so there is
no boundary condition). -/
private def genLoopZeroC (X : Type) [TopologicalSpace X] (x₀ a : X) : Ω^ (Fin 0) X x₀ :=
  ⟨ContinuousMap.const (Fin 0 → I) a, fun y hy => absurd hy (by simp [Cube.boundary])⟩

/-- Two such `0`-cubes are homotopic as soon as their values are joined by a path. -/
private theorem genLoopZeroC_homotopic {X : Type} [TopologicalSpace X] {x₀ a b : X}
    (p : Path a b) : GenLoop.Homotopic (genLoopZeroC X x₀ a) (genLoopZeroC X x₀ b) :=
  ⟨{ toFun := fun q : I × (Fin 0 → I) => p q.1
     continuous_toFun := p.continuous.comp continuous_fst
     map_zero_left := fun u => p.source
     map_one_left := fun u => p.target
     prop' := fun t u hu => absurd hu (by simp [Cube.boundary]) }⟩

/-- The map induced by `f` on `π₀` sends the class of `a` to the class of `f a`. -/
private theorem piMapN_zero_genLoopZeroC {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x₀ a : X) :
    piMapN f 0 x₀ ⟦genLoopZeroC X x₀ a⟧ = ⟦genLoopZeroC Y (f x₀) (f a)⟧ := by
  rw [piMapN_apply_mk]
  refine congrArg (Quotient.mk _) (Subtype.ext ?_)
  exact ContinuousMap.ext (fun u => rfl)

/-- **Injectivity of `π₀(f)` in geometric form**: if `f x₀` and `f x` are joined in `Y`, then `x₀`
and `x` are joined in `X`. -/
private theorem joined_of_piMapN_zero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x₀ : X) (hinj : Function.Injective (piMapN f 0 x₀))
    {x : X} (h : Joined (f x₀) (f x)) : Joined x₀ x := by
  obtain ⟨γ⟩ := h
  have h1 : (piMapN f 0 x₀ ⟦genLoopZeroC X x₀ x⟧ : HomotopyGroup (Fin 0) Y (f x₀))
      = piMapN f 0 x₀ ⟦genLoopZeroC X x₀ x₀⟧ := by
    rw [piMapN_zero_genLoopZeroC f x₀ x, piMapN_zero_genLoopZeroC f x₀ x₀]
    exact Quotient.sound (genLoopZeroC_homotopic γ.symm)
  have h2 : (⟦genLoopZeroC X x₀ x⟧ : HomotopyGroup (Fin 0) X x₀)
      = ⟦genLoopZeroC X x₀ x₀⟧ := hinj h1
  obtain ⟨H⟩ := Quotient.exact h2
  have hpath : Path x x₀ :=
    { toContinuousMap := ⟨fun t => H (t, fun _ => 0),
        H.continuous_toFun.comp (continuous_id.prodMk continuous_const)⟩
      source' := H.map_zero_left (fun _ => 0)
      target' := H.map_one_left (fun _ => 0) }
  exact Joined.symm ⟨hpath⟩

/-! ## Exactness at `π₂` of the base of the pair sequence (the `k = 0` case) -/

/-- **Exactness at `π₂(Y)` of the pair sequence of `g : Y → P`.** -/
private theorem pair_exact_two (g : C(Y, P)) (y₀ : Y) :
    Function.MulExact (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g y₀) 1
        (Work.RatHurewicz.homotopyFibreBasepoint g y₀))
      (Work.StemsB.πmap g 1 y₀) := by
  have h := Work.StemsB.les_exact_B (Work.RatHurewicz.homotopyFibreFst g y₀)
    (Work.RatHurewicz.homotopyFibreBasepoint g y₀) (Work.RatHurewicz.fibreHrel g y₀) 0
  have hcrux : Work.StemsB.dMap (Work.RatHurewicz.homotopyFibreFst g y₀)
      (Work.RatHurewicz.homotopyFibreBasepoint g y₀) (Work.RatHurewicz.fibreHrel g y₀) 0
      = (Work.RatHurewicz.pairShiftHom g y₀ 0).comp (Work.StemsB.πmap g 1 y₀) :=
    Work.RatHurewicz.fibreDMap_eq_pairShiftHom g y₀ 0
  have hcrux' : ∀ z, (Work.StemsB.dMap (Work.RatHurewicz.homotopyFibreFst g y₀)
      (Work.RatHurewicz.homotopyFibreBasepoint g y₀) (Work.RatHurewicz.fibreHrel g y₀) 0) z
      = (Work.RatHurewicz.pairShiftHom g y₀ 0) ((Work.StemsB.πmap g 1 y₀) z) :=
    fun z => congrFun (congrArg DFunLike.coe hcrux) z
  have hbij := (Work.RatHurewicz.pairShiftHom_bijective g y₀ 0).1
  intro y
  constructor
  · intro hy
    have hd : (Work.StemsB.dMap (Work.RatHurewicz.homotopyFibreFst g y₀)
        (Work.RatHurewicz.homotopyFibreBasepoint g y₀)
        (Work.RatHurewicz.fibreHrel g y₀) 0) y = 1 := by
      rw [hcrux', hy, map_one]
      rfl
    exact (h y).mp hd
  · intro hy
    have hd : (Work.StemsB.dMap (Work.RatHurewicz.homotopyFibreFst g y₀)
        (Work.RatHurewicz.homotopyFibreBasepoint g y₀)
        (Work.RatHurewicz.fibreHrel g y₀) 0) y = 1 :=
      (h y).mpr hy
    rw [hcrux'] at hd
    have hh : (Work.RatHurewicz.pairShiftHom g y₀ 0) ((Work.StemsB.πmap g 1 y₀) y)
        = (Work.RatHurewicz.pairShiftHom g y₀ 0) 1 := by
      rw [hd, map_one]
      rfl
    exact hbij hh

/-! ## Elementary consequences of `MulExact` -/

/-- If `MulExact f g` and `g` is injective then `f` is the zero map. -/
private theorem eq_one_of_mulExact_of_injective {M N Q : Type*} [Group M] [Group N] [Group Q]
    {f : M →* N} {g : N →* Q} (h : Function.MulExact f g) (hg : Function.Injective g) (x : M) :
    f x = 1 := by
  have h1 : g (f x) = 1 := (h (f x)).mpr ⟨x, rfl⟩
  exact hg (by rw [h1, map_one])

/-- If `MulExact f g` and the source of `f` is a subsingleton then `g` is injective. -/
private theorem eq_one_of_mulExact_of_subsingleton {M N Q : Type*} [Group M] [Group N] [Group Q]
    {f : M →* N} {g : N →* Q} (h : Function.MulExact f g) (hM : Subsingleton M) (y : N)
    (hy : g y = 1) : y = 1 := by
  haveI := hM
  obtain ⟨z, hz⟩ := (h y).mp hy
  rw [← hz, Subsingleton.elim z 1, map_one]

/-- If `MulExact f g` and `f` is the zero map then `g` is injective. -/
private theorem eq_one_of_mulExact_of_zero {M N Q : Type*} [Group M] [Group N] [Group Q]
    {f : M →* N} {g : N →* Q} (h : Function.MulExact f g) (hf : ∀ z, f z = 1) (y : N)
    (hy : g y = 1) : y = 1 := by
  obtain ⟨z, hz⟩ := (h y).mp hy
  rw [← hz, hf z]

/-! ## The main theorem -/

theorem serreConnectedCover (m N : ℕ) (hm : 1 ≤ m) (hmN : m < N) (Y : Type) [TopologicalSpace Y]
    (y₀ : Y) (P : Type) [TopologicalSpace P] (g : C(Y, P))
    (hg1 : ∀ i : ℕ, i ≤ m → Function.Bijective (Work.Serre.piMapN g i y₀))
    (hg2 : ∀ i : ℕ, m < i → i ≤ N → ∀ p : P, Subsingleton (HomotopyGroup (Fin i) P p)) :
    (∀ i : ℕ, i ≤ m → Subsingleton (HomotopyGroup (Fin i)
        (Work.RatHurewicz.homotopyFibre g y₀) (Work.RatHurewicz.homotopyFibreBasepoint g y₀))) ∧
    (∀ i : ℕ, m < i → i < N → Function.Bijective
        (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g y₀) (i - 1)
          (Work.RatHurewicz.homotopyFibreBasepoint g y₀))) := by
  constructor
  · -- ## `π_j(F) = 0` for `j ≤ m`
    intro j hj
    by_cases hj0 : j = 0
    · -- `j = 0`: `F` is path connected
      subst hj0
      have hsurj₁ : Function.Surjective (Work.StemsB.πmap g 0 y₀) := (hg1 1 hm).2
      have h0 : ∀ a : Y, Nonempty (Path (g y₀) (g a)) → Nonempty (Path y₀ a) :=
        fun a ha => joined_of_piMapN_zero_injective g y₀ (hg1 0 (by omega)).1 ha
      have hpc : PathConnectedSpace (Work.RatHurewicz.homotopyFibre g y₀) :=
        pathConnectedSpace_homotopyFibre g y₀ h0 hsurj₁
      have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre g y₀)) :=
        (pathConnectedSpace_iff_zerothHomotopy (X :=
          Work.RatHurewicz.homotopyFibre g y₀)).mp hpc |>.2
      exact ⟨fun x y => (HomotopyGroup.pi0EquivZerothHomotopy
        (X := Work.RatHurewicz.homotopyFibre g y₀)
        (x := Work.RatHurewicz.homotopyFibreBasepoint g y₀)).injective (hZ.elim _ _)⟩
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      by_cases hj1' : j = 1
      · -- `j = 1`: `π₁(F) = 0`
        subst hj1'
        by_cases hm1 : m = 1
        · have hP2 : Subsingleton (HomotopyGroup (Fin 2) P (g y₀)) :=
            hg2 2 (by omega) (by omega) (g y₀)
          exact piOneHomotopyFibreSubsingleton g y₀ (hg1 1 hm).1 hP2
        · have hm2 : 2 ≤ m := by omega
          exact piOneHomotopyFibreSubsingleton_of_surjective g y₀ (hg1 1 hm).1
            (hg1 2 hm2).2
      · -- `j ≥ 2`, written `j = k + 2`
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
        -- the pair sequence based at `k + 1`, and exactness at `π_{k+2}(Y)`
        obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les g y₀ (k + 1) (by omega)
        have hExY : Function.MulExact (Work.StemsB.πmap
              (Work.RatHurewicz.homotopyFibreFst g y₀) (k + 1)
              (Work.RatHurewicz.homotopyFibreBasepoint g y₀))
            (Work.StemsB.πmap g (k + 1) y₀) := by
          by_cases hk : k = 0
          · subst hk
            exact pair_exact_two g y₀
          · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
            obtain ⟨_, _, _, h2', _, _⟩ := Work.RatHurewicz.pair_les g y₀ k hk1
            exact h2'
        have hb : Function.Injective (Work.StemsB.πmap g (k + 1) y₀) := (hg1 (k + 2) hj).1
        -- the connecting map `d : π_{k+3}(P) → π_{k+2}(F)` is the zero map
        have hdzero : ∀ z : HomotopyGroup (Fin (k + 3)) P (g y₀), d z = 1 := by
          intro z
          by_cases hcase : k + 3 ≤ m
          · have hb3 : Function.Surjective (Work.StemsB.πmap g (k + 2) y₀) :=
              (hg1 (k + 3) hcase).2
            obtain ⟨w, hw⟩ := hb3 z
            exact (h3 z).mpr ⟨w, hw⟩
          · haveI hsub : Subsingleton (HomotopyGroup (Fin (k + 3)) P (g y₀)) :=
              hg2 (k + 3) (by omega) (by omega) (g y₀)
            rw [Subsingleton.elim z (1 : HomotopyGroup (Fin (k + 3)) P (g y₀)), map_one]
        -- `π_{k+2}(F) → π_{k+2}(Y)` is zero (image `= ker`, and `π_{k+2}(Y) → π_{k+2}(P)` injective)
        refine ⟨fun x y => ?_⟩
        have hzx : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g y₀) (k + 1)
            (Work.RatHurewicz.homotopyFibreBasepoint g y₀)) x = 1 :=
          eq_one_of_mulExact_of_injective hExY hb x
        have hzy : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g y₀) (k + 1)
            (Work.RatHurewicz.homotopyFibreBasepoint g y₀)) y = 1 :=
          eq_one_of_mulExact_of_injective hExY hb y
        exact (eq_one_of_mulExact_of_zero h4 hdzero x hzx).trans
          (eq_one_of_mulExact_of_zero h4 hdzero y hzy).symm
  · -- ## `π_i(F) → π_i(Y)` is bijective for `m < i < N`
    intro i hi hiN
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
    change Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g y₀) (k + 1)
      (Work.RatHurewicz.homotopyFibreBasepoint g y₀))
    obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les g y₀ (k + 1) (by omega)
    -- the connecting map out of `π_{k+3}(P)` is zero (`π_{k+3}(P) = 0` since `m < i + 1 ≤ N`)
    have hdzero : ∀ z : HomotopyGroup (Fin (k + 3)) P (g y₀), d z = 1 := by
      intro z
      haveI hsub : Subsingleton (HomotopyGroup (Fin (k + 3)) P (g y₀)) :=
        hg2 (k + 3) (by omega) (by omega) (g y₀)
      rw [Subsingleton.elim z (1 : HomotopyGroup (Fin (k + 3)) P (g y₀)), map_one]
    -- exactness at `π_{k+2}(Y)`
    have hExY : Function.MulExact (Work.StemsB.πmap
          (Work.RatHurewicz.homotopyFibreFst g y₀) (k + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint g y₀))
        (Work.StemsB.πmap g (k + 1) y₀) := by
      by_cases hk : k = 0
      · subst hk
        exact pair_exact_two g y₀
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        obtain ⟨_, _, _, h2', _, _⟩ := Work.RatHurewicz.pair_les g y₀ k hk1
        exact h2'
    constructor
    · -- injectivity: the kernel is `im d = 1`
      intro x y hxy
      have h1' : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g y₀) (k + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint g y₀)) (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      exact mul_inv_eq_one.mp (eq_one_of_mulExact_of_zero h4 hdzero (x * y⁻¹) h1')
    · -- surjectivity: the image is `ker(π_{k+2}(Y) → π_{k+2}(P))`, which is everything
      intro z
      haveI hsub : Subsingleton (HomotopyGroup (Fin (k + 2)) P (g y₀)) :=
        hg2 (k + 2) (by omega) (by omega) (g y₀)
      have hbz : (Work.StemsB.πmap g (k + 1) y₀) z
          = (1 : HomotopyGroup (Fin (k + 2)) P (g y₀)) := Subsingleton.elim _ _
      exact (hExY z).mp hbz

end

end Work.Serre
