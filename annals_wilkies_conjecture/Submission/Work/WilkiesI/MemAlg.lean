/-
Area I, part 2: the `alg` API and the area I theorem.

`X.alg` (frozen, `ChallengeDeps`) is the union of the semialgebraic, connected, infinite
subsets of `X`.  The main result here, `I_mem_alg`, says that a *local algebraic graph*
inside `X` lies in `X.alg`:  if `V` is semialgebraic, `p ∈ V`, and on a box around `p` the
set `V` is the image of an open `U ⊆ ℝ^μ` (μ > 0) under a continuous section `ψ` of the
coordinate projection along `e`, then `p ∈ X.alg` whenever that piece of `V` is contained
in `X`.

The set that witnesses `p ∈ X.alg` is
`Y = V ∩ B ∩ {|x∘e - p∘e| < η}` for `η > 0` small enough that the ball of radius `η`
about `t₀ = p ∘ e` lies in `U`.  Then `Y = ψ '' Metric.ball t₀ η` is the continuous
injective image of a ball, hence semialgebraic, infinite and connected.  In the area
statement `B` is the box `{|x - p| < δ}`, but the argument only uses that `B` is
semialgebraic and contains `p`; the general form is `mem_alg_of_local_graph`.
-/
import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesI.Basic
import Submission.Work.WilkiesI.BallInfinite
import Submission.Work.WilkiesI.InjOnCoordSection
import Submission.Work.WilkiesI.ImageBallEq
import Submission.Work.WilkiesI.ConnectedImageBall

set_option autoImplicit false
noncomputable section
open Classical
open FirstOrder FirstOrder.Language

namespace Work.WilkiesI

open WilkiesConjecture

variable {n : ℕ}

/-! ## 1. The `alg` API -/

/-- A point of a semialgebraic, infinite, connected subset of `X` lies in `X.alg`. -/
theorem mem_alg_of {n : ℕ} {X Y : Set (Fin n → ℝ)} (hYX : Y ⊆ X) (hY : IsSemialgebraic Y)
    (hinf : Y.Infinite) (hc : IsConnected Y) {p : Fin n → ℝ} (hp : p ∈ Y) : p ∈ X.alg := by
  show p ∈ sSup {Z : Set (Fin n → ℝ) | Z ⊆ X ∧ IsSemialgebraic Z ∧ Z.Infinite ∧ IsConnected Z}
  rw [Set.sSup_eq_sUnion, Set.mem_sUnion]
  exact ⟨Y, ⟨hYX, hY, hinf, hc⟩, hp⟩

/-- `X.alg` is contained in `X` (it is a union of subsets of `X`). -/
theorem alg_subset (X : Set (Fin n → ℝ)) : X.alg ⊆ X := by
  intro p hp
  have hp' : p ∈ sSup {Z : Set (Fin n → ℝ) | Z ⊆ X ∧ IsSemialgebraic Z ∧ Z.Infinite ∧
      IsConnected Z} := hp
  rw [Set.sSup_eq_sUnion, Set.mem_sUnion] at hp'
  obtain ⟨A, hA, hpA⟩ := hp'
  exact hA.1 hpA

/-- `X ↦ X.alg` is monotone.  (Area D uses this to push a truncation `X_M ⊆ X` into `alg`.) -/
theorem alg_mono {X Y : Set (Fin n → ℝ)} (h : X ⊆ Y) : X.alg ⊆ Y.alg := by
  intro p hp
  have hp' : p ∈ sSup {Z : Set (Fin n → ℝ) | Z ⊆ X ∧ IsSemialgebraic Z ∧ Z.Infinite ∧
      IsConnected Z} := hp
  show p ∈ sSup {Z : Set (Fin n → ℝ) | Z ⊆ Y ∧ IsSemialgebraic Z ∧ Z.Infinite ∧ IsConnected Z}
  rw [Set.sSup_eq_sUnion, Set.mem_sUnion] at hp' ⊢
  obtain ⟨A, hA, hpA⟩ := hp'
  exact ⟨A, ⟨hA.1.trans h, hA.2.1, hA.2.2.1, hA.2.2.2⟩, hpA⟩

/-- `X.alg` is exactly the union of the semialgebraic connected infinite subsets of `X`. -/
theorem alg_eq_sUnion (X : Set (Fin n → ℝ)) :
    X.alg = ⋃₀ {Z : Set (Fin n → ℝ) | Z ⊆ X ∧ IsSemialgebraic Z ∧ Z.Infinite ∧ IsConnected Z} :=
  Set.sSup_eq_sUnion _

/-- Extraction form of the definition of `X.alg`: a point of `X.alg` is a point of a
semialgebraic, infinite, connected subset of `X`. -/
theorem exists_subset_of_mem_alg {X : Set (Fin n → ℝ)} {p : Fin n → ℝ} (hp : p ∈ X.alg) :
    ∃ Y : Set (Fin n → ℝ), Y ⊆ X ∧ IsSemialgebraic Y ∧ Y.Infinite ∧ IsConnected Y ∧ p ∈ Y := by
  rw [alg_eq_sUnion, Set.mem_sUnion] at hp
  obtain ⟨Y, hY, hpY⟩ := hp
  exact ⟨Y, hY.1, hY.2.1, hY.2.2.1, hY.2.2.2, hpY⟩

/-- A semialgebraic, infinite, connected set is contained in its own `alg` (so `X.alg = X`
for such `X`). -/
theorem subset_alg_self {X : Set (Fin n → ℝ)} (h : IsSemialgebraic X) (hinf : X.Infinite)
    (hc : IsConnected X) : X ⊆ X.alg :=
  fun _ hp => mem_alg_of (Set.Subset.refl X) h hinf hc hp

/-! ## 2. The local graph is the image of a ball -/

/-- **The key set identity.**  If `V` coincides with the image of the section `ψ` on the
piece `V ∩ B`, then the further slice in which the `e`-coordinates stay `η`-close to those
of `p = ψ t₀` is exactly the image of the ball of radius `η` around `t₀`.

(`B` is an arbitrary set here; the box case `B = {|x - p| < δ}` is
`Work.WilkiesI.ImageBallEq`.) -/
theorem image_ball_eq_of_section {n μ : ℕ} (e : Fin μ ↪ Fin n) {U : Set (Fin μ → ℝ)}
    {ψ : (Fin μ → ℝ) → (Fin n → ℝ)} (hsec : ∀ t ∈ U, ψ t ∘ e = t)
    {V B : Set (Fin n → ℝ)} (hgraph : V ∩ B = ψ '' U) {t₀ : Fin μ → ℝ} (ht₀ : t₀ ∈ U)
    {p : Fin n → ℝ} (hψt₀ : ψ t₀ = p) {η : ℝ} (hη : 0 < η) (hball : Metric.ball t₀ η ⊆ U) :
    V ∩ B ∩ {x : Fin n → ℝ | ∀ j, |x (e j) - p (e j)| < η} = ψ '' Metric.ball t₀ η := by
  have hpj : ∀ j : Fin μ, p (e j) = t₀ j := fun j => by
    rw [← hψt₀]; exact congr_fun (hsec t₀ ht₀) j
  ext x
  constructor
  · rintro ⟨⟨hV, hB⟩, hE⟩
    have hx : x ∈ ψ '' U := by rw [← hgraph]; exact ⟨hV, hB⟩
    obtain ⟨t, htU, htx⟩ := hx
    refine ⟨t, ?_, htx⟩
    rw [Metric.mem_ball, dist_pi_lt_iff hη]
    intro j
    have h1 : x (e j) = t j := by rw [← htx]; exact congr_fun (hsec t htU) j
    have h3 : |x (e j) - p (e j)| < η := hE j
    rw [h1, hpj j] at h3
    simpa [Real.dist_eq] using h3
  · rintro ⟨t, ht, htx⟩
    have htU : t ∈ U := hball ht
    subst htx
    have hmem : ψ t ∈ V ∩ B := by rw [hgraph]; exact ⟨t, htU, rfl⟩
    refine ⟨⟨hmem.1, hmem.2⟩, fun j => ?_⟩
    have h1 : ψ t (e j) = t j := congr_fun (hsec t htU) j
    have h3 : |t j - t₀ j| < η := by
      have hd : dist t t₀ < η := Metric.mem_ball.mp ht
      have := lt_of_le_of_lt (dist_le_pi_dist t t₀ j) hd
      rwa [Real.dist_eq] at this
    rw [h1, hpj j]
    exact h3

/-! ## 3. The area I theorem -/

/-- **Area I, general form.**  A local algebraic graph inside `X` lies in `X.alg`.

`V` and `B` are semialgebraic, `p ∈ V ∩ B`, and on `V ∩ B` the set `V` coincides with the
image of an open `U ⊆ ℝ^μ` (`μ > 0`) under a continuous section `ψ` of the coordinate
projection along `e`.  If `V ∩ B ⊆ X` then `p ∈ X.alg`. -/
theorem mem_alg_of_local_graph {n μ : ℕ} (hμ : 0 < μ) (X V B : Set (Fin n → ℝ))
    (hV : IsSemialgebraic V) (hB : IsSemialgebraic B) (p : Fin n → ℝ) (hpB : p ∈ B)
    (e : Fin μ ↪ Fin n) (U : Set (Fin μ → ℝ)) (hU : IsOpen U)
    (ψ : (Fin μ → ℝ) → (Fin n → ℝ)) (hψ : ContinuousOn ψ U)
    (hsec : ∀ t ∈ U, ψ t ∘ e = t) (hgraph : V ∩ B = ψ '' U)
    (hpV : p ∈ V) (hX : V ∩ B ⊆ X) : p ∈ X.alg := by
  -- `p = ψ t₀` with `t₀ ∈ U`
  have hpU : p ∈ ψ '' U := by rw [← hgraph]; exact ⟨hpV, hpB⟩
  obtain ⟨t₀, ht₀U, ht₀p⟩ := hpU
  -- a ball around `t₀` inside the open set `U`
  obtain ⟨η, hη, hηU⟩ := Metric.isOpen_iff.mp hU t₀ ht₀U
  have hkey := image_ball_eq_of_section e hsec hgraph ht₀U ht₀p hη hηU
  -- the witnessing set
  refine mem_alg_of (Y := V ∩ B ∩ {x : Fin n → ℝ | ∀ j, |x (e j) - p (e j)| < η})
    ?_ ?_ ?_ ?_ ?_
  · exact fun x hx => hX hx.1
  · exact isSemialgebraic_inter (isSemialgebraic_inter hV hB) (isSemialgebraic_eBox e p η)
  · rw [hkey]
    exact (Set.infinite_image_iff ((InjOnCoordSection e hsec).mono hηU)).mpr
      (BallInfinite hμ t₀ hη)
  · rw [hkey]
    exact ConnectedImageBall hψ hη hηU
  · rw [hkey]
    exact ⟨t₀, by rw [Metric.mem_ball, dist_self]; exact hη, ht₀p⟩

/-- **Area I.**  A local algebraic graph inside `X` lies in `X.alg`.

`V` is semialgebraic and coincides, inside the box `{|x - p| < δ}`, with the image of an
open `U ⊆ ℝ^μ` (`μ > 0`) under a continuous section `ψ` of the coordinate projection along
`e`.  Then `p ∈ X.alg` provided that piece of `V` lies in `X`. -/
theorem I_mem_alg {n μ : ℕ} (hμ : 0 < μ) (X V : Set (Fin n → ℝ)) (hV : IsSemialgebraic V)
    (p : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (e : Fin μ ↪ Fin n)
    (U : Set (Fin μ → ℝ)) (hU : IsOpen U) (ψ : (Fin μ → ℝ) → (Fin n → ℝ))
    (hψ : ContinuousOn ψ U) (hsec : ∀ t ∈ U, ψ t ∘ e = t)
    (hgraph : V ∩ {x | ∀ i, |x i - p i| < δ} = ψ '' U)
    (hpV : p ∈ V) (hX : V ∩ {x | ∀ i, |x i - p i| < δ} ⊆ X) : p ∈ X.alg := by
  have hbox : p ∈ {x : Fin n → ℝ | ∀ i, |x i - p i| < δ} := by
    intro i
    simpa using hδ
  exact mem_alg_of_local_graph hμ X V _ hV (isSemialgebraic_box p δ) p hbox e U hU ψ hψ hsec
    hgraph hpV hX

/-- Area I for a polynomial hypersurface: the "local algebraic graph" is the zero set of a
polynomial `P` (intersected with the box).  This is the form in which area H consumes the
statement: `V` is a hypersurface and `p` a regular point of it. -/
theorem mem_alg_of_zeroLocus {n μ : ℕ} (hμ : 0 < μ) (X : Set (Fin n → ℝ))
    (P : MvPolynomial (Fin n) ℝ) (p : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (e : Fin μ ↪ Fin n)
    (U : Set (Fin μ → ℝ)) (hU : IsOpen U) (ψ : (Fin μ → ℝ) → (Fin n → ℝ))
    (hψ : ContinuousOn ψ U) (hsec : ∀ t ∈ U, ψ t ∘ e = t)
    (hgraph : {x : Fin n → ℝ | (MvPolynomial.eval x) P = 0} ∩
        {x | ∀ i, |x i - p i| < δ} = ψ '' U)
    (hp : (MvPolynomial.eval p) P = 0)
    (hX : {x : Fin n → ℝ | (MvPolynomial.eval x) P = 0} ∩
        {x | ∀ i, |x i - p i| < δ} ⊆ X) : p ∈ X.alg :=
  I_mem_alg hμ X _ (isSemialgebraic_eval_eq P 0) p δ hδ e U hU ψ hψ hsec hgraph hp hX

end Work.WilkiesI

namespace WilkiesDesign

open WilkiesConjecture

/-- **Area I (delivered form).**  Identical statement to `WilkiesDesign.I_mem_alg` in
`Submission/Work/Wilkies/Holes.lean`, proved in `Submission/Work/WilkiesI/`. -/
theorem I_mem_alg_proved {n μ : ℕ} (hμ : 0 < μ) (X V : Set (Fin n → ℝ)) (hV : IsSemialgebraic V)
    (p : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (e : Fin μ ↪ Fin n)
    (U : Set (Fin μ → ℝ)) (hU : IsOpen U) (ψ : (Fin μ → ℝ) → (Fin n → ℝ))
    (hψ : ContinuousOn ψ U) (hsec : ∀ t ∈ U, ψ t ∘ e = t)
    (hgraph : V ∩ {x | ∀ i, |x i - p i| < δ} = ψ '' U)
    (hpV : p ∈ V) (hX : V ∩ {x | ∀ i, |x i - p i| < δ} ⊆ X) : p ∈ X.alg :=
  Work.WilkiesI.I_mem_alg hμ X V hV p δ hδ e U hU ψ hψ hsec hgraph hpV hX

end WilkiesDesign
