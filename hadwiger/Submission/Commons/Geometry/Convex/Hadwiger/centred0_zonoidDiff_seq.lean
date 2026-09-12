import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.hausdorffDist_eq_sSup_support
import Submission.Commons.Geometry.Convex.Hadwiger.support_add
import Submission.Commons.Geometry.Convex.Hadwiger.eq_of_support_eq
import Submission.Commons.Geometry.Convex.Hadwiger.smoothCentred_dense
import Submission.Commons.Geometry.Convex.Hadwiger.smoothCentred_generalizedZonoid

/-!
# `centred0_zonoidDiff_seq` — origin-symmetric bodies are limits of differences of zonoids

**Statement** (requested by the `klain333_from_cylinders` development; the
analytic core of Klain, *A short proof of Hadwiger's characterization
theorem*, Mathematika 42 (1995) 329–339, Prop. 3.1 (p. 333), together with
Schneider, *Convex Bodies*, Thm 3.4.1):
every *origin-symmetric* convex body `K` (`(K : Set V) = -(K : Set V)`) is a
Hausdorff limit of convex bodies `K_j` each of which is a *generalized
zonoid*: there are zonoids `Y₁`, `Y₂` — spelled out as Hausdorff limits of
`[0,1]`-box zonotopes `Zᵢ(n) = {Σᵢ tᵢ • wᵢ(n,i) : tᵢ ∈ [0,1]}` — with
`K_j + Y₂ = Y₁`.

## Proof plan (mathematics)

1. (polytope density, commons `polytope_dense`, + symmetrization) it
   suffices to approximate origin-symmetric polytopes `Q` by generalized
   zonoids;
2. (Schneider Thm 3.4.1, to be developed) approximate `h_Q` uniformly on the
   unit sphere by even `C∞` positively homogeneous sublinear functions
   `h_m` (support functions of origin-symmetric convex bodies with smooth
   support functions);
3. (cosine transform / Funk–Hecke surjectivity onto even smooth functions;
   Klain–Rota Prop 8.1.2, to be developed) write `h_m = C g_m` with `g_m`
   even smooth and `g_m = g_m⁺ − g_m⁻`; for even `g ≥ 0` one has
   `Cg(u) = ∫_S max 0 ⟨u,x⟩ g(x) dσ(x)`, an even sublinear zonoid support
   function, so `X_m + Y₂ = Y₁` with `X_m := body(h_m)` (≈ `Q`),
   `Y₁ := body(Cg_m⁺)`, `Y₂ := body(Cg_m⁻)` — by additivity and injectivity
   of support functions (commons `support_add`, `eq_of_support_eq`);
4. (Riemann sums, to be developed) each `Yᵢ` is a Hausdorff limit of
   `[0,1]`-box zonotopes (the `Z` sequences of the statement), because
   `Cg₊` is a uniform limit of the finite box-zonotope support functions
   `Σⱼ max 0 ⟨u,xⱼ⟩ g₊(xⱼ) Δσⱼ`.

The single analytic core is isolated as `analytic_core` below (the per-`ε`
version of the target with `IsZonoidLimit` spelled out); the main theorem is
the elementary assembly of that core into a sequence.
-/

namespace Commons.Geometry.Convex.Hadwiger

open Filter Metric Set
open scoped Topology BigOperators Pointwise Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-! ## `[0,1]`-box zonotopes

The box-zonotope API (`boxZono`, `boxZonoBody`, `boxZono_support`, ...) is
provided by the commons module
`Commons.Geometry.Convex.Hadwiger.zonoidLimit_of_continuous_even_nonneg`;
we only add the set-form rewrite used below. -/

/-! ## the analytic core

The two theorems below are the mathematical heart:

1. `smoothCentred_dense_here` (→ commons `smoothCentred_dense`,
   Schneider Thm 3.4.1): origin-symmetric convex bodies with `C∞` support
   functions are Hausdorff-dense among origin-symmetric convex bodies;
2. `smoothCentred_generalizedZonoid_here` (→ commons
   `smoothCentred_generalizedZonoid`, Klain–Rota Prop. 8.1.2, Funk–Hecke /
   cosine transform): an origin-symmetric body with `C∞` support function is
   a *generalized zonoid* `X + Y₂ = Y₁` with `Y₁`, `Y₂` limits of
   `[0,1]`-box zonotopes.

Both pillars are proved in the commons and imported above;
`analytic_core` is the per-`ε` version of the target and follows from them by
composition; the main theorem assembles `analytic_core` into a sequence. -/

/-- per-`ε` analytic core: every origin-symmetric body admits a generalized
zonoid arbitrarily close in the Hausdorff metric. -/
theorem analytic_core (K : ConvexBody V)
    (hK : (K : Set V) = -(K : Set V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ConvexBody V,
      dist X K < ε ∧
      ∃ (Y₁ Y₂ : ConvexBody V) (Z₁ Z₂ : ℕ → ConvexBody V)
        (k₁ k₂ : ℕ → ℕ) (w₁ : ∀ n : ℕ, Fin (k₁ n) → V) (w₂ : ∀ n : ℕ, Fin (k₂ n) → V),
        Tendsto Z₁ atTop (𝓝 Y₁) ∧ Tendsto Z₂ atTop (𝓝 Y₂) ∧
        (∀ n : ℕ, (Z₁ n : Set V) = boxZono (k₁ n) (w₁ n)) ∧
        (∀ n : ℕ, (Z₂ n : Set V) = boxZono (k₂ n) (w₂ n)) ∧
        X + Y₂ = Y₁ := by
  -- 1. smooth origin-symmetric X within ε of K (Schneider 3.4.1)
  rcases smoothCentred_dense V K hK hε with ⟨X, hXdist, hXsym, hXsmooth⟩
  -- 2. X is a generalized zonoid (Klain–Rota 8.1.2 / cosine transform)
  rcases smoothCentred_generalizedZonoid V X hXsym hXsmooth with
    ⟨Y₁, Y₂, Z₁, Z₂, k₁, k₂, w₁, w₂, hT1, hT2, hc1, hc2, heq⟩
  refine ⟨X, hXdist, Y₁, Y₂, Z₁, Z₂, k₁, k₂, w₁, w₂, hT1, hT2, ?_, ?_, heq⟩
  · intro n
    rw [hc1 n]
    exact (boxZono_eq_set (k₁ n) (w₁ n)).symm
  · intro n
    rw [hc2 n]
    exact (boxZono_eq_set (k₂ n) (w₂ n)).symm

/-! ## assembly: per-`ε` core ⇒ converging sequence -/

lemma tendsto_one_div_add_one : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (𝓝 0) := by
  have hfun : (fun j : ℕ => (1 : ℝ) / (j + 1)) =
      (fun n : ℕ => (1 : ℝ) / (n : ℝ)) ∘ (fun a : ℕ => a + 1) := by
    funext j
    norm_num [Nat.cast_add]
  rw [hfun]
  exact (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)

/-! ## the main statement -/

theorem centred0_zonoidDiff_seq
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (K : ConvexBody V)
    (hK : (K : Set V) = -(K : Set V)) :
    ∃ Kj : ℕ → ConvexBody V,
      Tendsto Kj atTop (𝓝 K) ∧
      ∀ j : ℕ, ∃ (Y₁ Y₂ : ConvexBody V) (Z₁ Z₂ : ℕ → ConvexBody V)
        (k₁ k₂ : ℕ → ℕ) (w₁ : ∀ n : ℕ, Fin (k₁ n) → V) (w₂ : ∀ n : ℕ, Fin (k₂ n) → V),
        Tendsto Z₁ atTop (𝓝 Y₁) ∧ Tendsto Z₂ atTop (𝓝 Y₂) ∧
        (∀ n : ℕ, (Z₁ n : Set V) =
          {x : V | ∃ t : Fin (k₁ n) → ℝ, (∀ i : Fin (k₁ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
            x = ∑ i : Fin (k₁ n), t i • w₁ n i}) ∧
        (∀ n : ℕ, (Z₂ n : Set V) =
          {x : V | ∃ t : Fin (k₂ n) → ℝ, (∀ i : Fin (k₂ n), t i ∈ Set.Icc (0 : ℝ) 1) ∧
            x = ∑ i : Fin (k₂ n), t i • w₂ n i}) ∧
        Kj j + Y₂ = Y₁ := by
  classical
  let core : ∀ j : ℕ, ∃ X : ConvexBody V, dist X K < (1 : ℝ) / (j + 1) ∧
      ∃ (Y₁ Y₂ : ConvexBody V) (Z₁ Z₂ : ℕ → ConvexBody V)
        (k₁ k₂ : ℕ → ℕ) (w₁ : ∀ n : ℕ, Fin (k₁ n) → V) (w₂ : ∀ n : ℕ, Fin (k₂ n) → V),
        Tendsto Z₁ atTop (𝓝 Y₁) ∧ Tendsto Z₂ atTop (𝓝 Y₂) ∧
        (∀ n : ℕ, (Z₁ n : Set V) = boxZono (k₁ n) (w₁ n)) ∧
        (∀ n : ℕ, (Z₂ n : Set V) = boxZono (k₂ n) (w₂ n)) ∧
        X + Y₂ = Y₁ := fun j => by
      have hpos : 0 < (1 : ℝ) / (j + 1) := by positivity
      exact analytic_core K hK hpos
  let Kj : ℕ → ConvexBody V := fun j => Classical.choose (core j)
  refine ⟨Kj, ?_, ?_⟩
  · have hd0 : ∀ j : ℕ, 0 ≤ dist (Kj j) K := fun j => dist_nonneg
    have hdle : ∀ j : ℕ, dist (Kj j) K ≤ (1 : ℝ) / (j + 1) := by
      intro j
      have hspec := Classical.choose_spec (core j)
      exact le_of_lt (by simpa [Kj] using hspec.1)
    have hdlim : Tendsto (fun j : ℕ => dist (Kj j) K) atTop (𝓝 0) :=
      squeeze_zero hd0 hdle tendsto_one_div_add_one
    exact (tendsto_iff_dist_tendsto_zero).2 hdlim
  · intro j
    rcases Classical.choose_spec (core j) with ⟨hXj, hw⟩
    rcases hw with ⟨Y₁, Y₂, Z₁, Z₂, k₁, k₂, w₁, w₂, hT1, hT2, hc1, hc2, heq⟩
    refine ⟨Y₁, Y₂, Z₁, Z₂, k₁, k₂, w₁, w₂, hT1, hT2, ?_, ?_, ?_⟩
    · intro n
      rw [hc1 n]
      exact boxZono_eq_set (k₁ n) (w₁ n)
    · intro n
      rw [hc2 n]
      exact boxZono_eq_set (k₂ n) (w₂ n)
    · simpa [Kj] using heq

end
end Commons.Geometry.Convex.Hadwiger
