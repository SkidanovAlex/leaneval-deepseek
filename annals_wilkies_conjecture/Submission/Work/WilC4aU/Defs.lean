/-
  Area C4aU (Wilkie's conjecture for Pfaffian structures): uniformity of the exponent set in
  `PolyBoundedRExp`. This is the hole `C4a_uniform` of `WilkiesDesign.CG.C4a` (spec
  `Submission/Work/Wilkies/CG/C4a/Spec.lean`).

  Design (see `Submission/Work/Wilkies/CG/C4a/DESIGN.md`, step 4 "Uniformity"):
  for a rexp-existential family `Y` with unique section `f_c`, the value `2 ^ (q c)` is the limit
  of the ratio `f_c (2 x) / f_c x`; the set of these limits is existentially definable (it is a
  cluster-value set of the ratio), hence countable (`q` is rational), hence finite by uniform
  finiteness (`hUF` at `k = 0`).  The finite exponent set `Qs` is then the preimage of that finite
  set under `q ↦ 2 ^ q`.

  This file contains the definitions and the small auxiliary API.

  Main definitions:
  * `ZeroSect Y c`, `AsymSect Y c q a` : the two disjuncts of `PBOne Y c`;
  * `RatioCluster Y c lam` : `lam` is a cluster value of `y' / y` along `x → ∞`, `x ↦ 2 x`, on
    the fibre of `Y` over `c` (with the side condition that the fibre has points `x` with `y ≠ 0`
    for arbitrarily large `x`, expressed division-free by `1 ≤ ε * x`);
  * `ClusterSet Y : Set ℝ`, `ClusterFam Y : Set (Fin 1 → ℝ)` : the cluster values over all
    parameters.
-/
import Submission.Work.Wilkies.CG.C4a.Spec
import Submission.Work.WilC0.Compl
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Classical Topology
namespace Work.WilC4aU

open WilkiesDesign (RExpExist rexp rexpPolyEval)
open WilkiesDesign.CG.C4a (PBOne)
open Work.WilC0

/-! ## 1. The two disjuncts of `PBOne` -/

/-- First disjunct of `PBOne`: the section is eventually zero. -/
def ZeroSect {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) : Prop :=
  ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → Fin.cons x (Fin.cons y c) ∈ Y → y = 0

/-- Second disjunct of `PBOne`: the section is asymptotic to `a * x ^ q`, `a ≠ 0`. -/
def AsymSect {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (q : ℚ) (a : ℝ) : Prop :=
  a ≠ 0 ∧ ∀ ε > (0 : ℝ), ∃ R : ℝ, ∀ x y : ℝ, R ≤ x →
    Fin.cons x (Fin.cons y c) ∈ Y → |y / x ^ (q : ℝ) - a| < ε

/-- `PBOne` is exactly the disjunction of `ZeroSect` and of the existence of asymptotic data. -/
theorem pbOne_iff {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) :
    PBOne Y c ↔ ZeroSect Y c ∨ ∃ (q : ℚ) (a : ℝ), AsymSect Y c q a := Iff.rfl

theorem zeroSect_of_pbOne_first {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ}
    (h : ZeroSect Y c) : PBOne Y c := Or.inl h

/-- If the fibre has points `(x, y)` with `y ≠ 0` for arbitrarily large `x`, then `ZeroSect` fails. -/
theorem not_zeroSect_of_unbounded {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ}
    (h : ∀ R : ℝ, ∃ x ≥ R, ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y ∧ y ≠ 0) :
    ¬ ZeroSect Y c := by
  rintro ⟨R, hR⟩
  obtain ⟨x, hxR, y, hxy, hy⟩ := h R
  exact hy (hR x y hxR hxy)

/-! ## 2. Cluster values of the ratio `f (2 x) / f x` -/

/-- `lam` is a cluster value of `y' / y` along `x → ∞` with `x ↦ 2 * x`, over the fibre of `Y`
at `c`.  The condition `1 ≤ ε * x` says that there are witnesses for every scale `ε > 0`, i.e.
that the fibre has points with `y ≠ 0` for arbitrarily large `x`; the last inequality is
`|y' / y - lam| < ε` written without division. -/
def RatioCluster {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (lam : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ x y y' : ℝ, 1 ≤ ε * x ∧ Fin.cons x (Fin.cons y c) ∈ Y ∧ y ≠ 0 ∧
    Fin.cons (2 * x) (Fin.cons y' c) ∈ Y ∧ (y' - lam * y) ^ 2 < ε ^ 2 * y ^ 2

/-- The division-free inequality is the ratio inequality. -/
theorem sq_lt_sq_iff_ratio {y y' lam ε : ℝ} (hy : y ≠ 0) (hε : 0 < ε) :
    (y' - lam * y) ^ 2 < ε ^ 2 * y ^ 2 ↔ |y' / y - lam| < ε := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hsplit : y' - lam * y = y * (y' / y - lam) := by
    field_simp
  rw [hsplit, mul_pow, mul_comm (ε ^ 2) (y ^ 2), mul_lt_mul_iff_right₀ hy2, sq_lt_sq,
    abs_of_pos hε]

/-- From the cluster condition one gets points with `y ≠ 0` for arbitrarily large `x`. -/
theorem unbounded_of_ratioCluster {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ}
    {lam : ℝ} (h : RatioCluster Y c lam) :
    ∀ R : ℝ, ∃ x ≥ R, ∃ y : ℝ, Fin.cons x (Fin.cons y c) ∈ Y ∧ y ≠ 0 := by
  intro R
  set ε : ℝ := 1 / (max R 1 + 1) with hεdef
  have hMpos : 0 < max R 1 + 1 := by positivity
  have hε : 0 < ε := by positivity
  obtain ⟨x, y, y', hx, hxy, hy, -, -⟩ := h ε hε
  have h1 : 1 / ε = max R 1 + 1 := by
    rw [hεdef, one_div_one_div]
  have hx' : 1 / ε ≤ x := by
    rw [div_le_iff₀ hε]
    simpa [mul_comm] using hx
  rw [h1] at hx'
  have hle : max R 1 + 1 ≤ x := hx'
  have hle2 : max R 1 ≤ x := le_trans (le_add_of_nonneg_right zero_le_one) hle
  exact ⟨x, le_trans (le_max_left R 1) hle2, y, hxy, hy⟩

/-- The cluster-value set of a family, over all parameters. -/
def ClusterSet {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set ℝ :=
  {lam | ∃ c : Fin k → ℝ, RatioCluster Y c lam}

/-- The same set, shaped as a set of one-tuples (the shape of `RExpExist`). -/
def ClusterFam {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin 1 → ℝ) :=
  {v | v 0 ∈ ClusterSet Y}

@[simp] theorem mem_clusterFam {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {v : Fin 1 → ℝ} :
    v ∈ ClusterFam Y ↔ v 0 ∈ ClusterSet Y := Iff.rfl

@[simp] theorem mem_clusterSet {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {lam : ℝ} :
    lam ∈ ClusterSet Y ↔ ∃ c : Fin k → ℝ, RatioCluster Y c lam := Iff.rfl

/-- The constant-tuple map, an injection `ℝ → (Fin 1 → ℝ)`. -/
theorem injective_const_fin1 : Function.Injective (fun a : ℝ => fun _ : Fin 1 => a) := by
  intro a b h
  simpa using congrFun h 0

/-- The one-tuple of a cluster value is a cluster value. -/
theorem clusterFam_iff (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (lam : ℝ) :
    (fun _ : Fin 1 => lam) ∈ ClusterFam Y ↔ lam ∈ ClusterSet Y := Iff.rfl

theorem countable_clusterSet_iff {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    (ClusterSet Y).Countable ↔ (ClusterFam Y).Countable := by
  have hfam : ClusterFam Y = (fun lam : ℝ => fun _ : Fin 1 => lam) '' ClusterSet Y := by
    ext v
    constructor
    · intro hv
      exact ⟨v 0, hv, funext fun i => by fin_cases i; rfl⟩
    · rintro ⟨lam, hl, rfl⟩
      exact hl
  have hset : ClusterSet Y = (fun v : Fin 1 → ℝ => v 0) '' ClusterFam Y := by
    ext lam
    constructor
    · intro hl
      exact ⟨fun _ => lam, hl, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
  constructor
  · intro h
    rw [hfam]
    exact h.image _
  · intro h
    rw [hset]
    exact h.image _

/-- A finite cluster-value family gives a finite cluster-value set. -/
theorem finite_clusterSet_of_fam {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (h : (ClusterFam Y).Finite) : (ClusterSet Y).Finite := by
  have hset : ClusterSet Y = (fun v : Fin 1 → ℝ => v 0) '' ClusterFam Y := by
    ext lam
    constructor
    · intro hl
      exact ⟨fun _ => lam, hl, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
  rw [hset]
  exact h.image _

/-! ## 3. Auxiliary closure API for the existential-definability calculus -/

/-- Adjoining unused coordinates on the right. -/
theorem rexExistI_castAdd {n r : ℕ} {X : Set (Fin n → ℝ)} (hX : RExpExistI X) :
    RExpExistI {z : Fin (n + r) → ℝ | (fun i => z (Fin.castAdd r i)) ∈ X} :=
  hX.pullback (Fin.castAdd r)

/-- Projecting away a block of `r` existential witnesses at the end of a `Fin`-tuple. -/
theorem rexExistI_existsBlockFin {n r : ℕ} {X : Set (Fin (n + r) → ℝ)}
    (hX : RExpExistI X) :
    RExpExistI {z : Fin n → ℝ | ∃ u : Fin r → ℝ, Fin.append z u ∈ X} := by
  have h1 : RExpExistI {w : (Fin n ⊕ Fin r) → ℝ |
      w ∘ ⇑(finSumFinEquiv (m := n) (n := r)).symm ∈ X} :=
    hX.pullback ⇑(finSumFinEquiv (m := n) (n := r)).symm
  refine (h1.existsBlock (μ := Fin r)).of_eq ?_
  ext z
  constructor
  · rintro ⟨u, hu⟩
    rw [Set.mem_ofPred_eq] at hu
    exact ⟨u, by rwa [sumElim_comp_finSumFinEquiv_symm] at hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, by rw [Set.mem_ofPred_eq, sumElim_comp_finSumFinEquiv_symm]; exact hu⟩

/-- Projecting away the last coordinate. -/
theorem rexExistI_existsFin {n : ℕ} {X : Set (Fin (n + 1) → ℝ)} (hX : RExpExistI X) :
    RExpExistI {z : Fin n → ℝ | ∃ a : ℝ, Fin.append z ![a] ∈ X} := by
  have h1 : RExpExistI {z : Fin n → ℝ | ∃ u : Fin 1 → ℝ, Fin.append z u ∈ X} :=
    rexExistI_existsBlockFin hX
  refine h1.of_eq ?_
  ext z
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u 0, by rwa [show u = ![u 0] from funext fun i => by fin_cases i; simp] at hu⟩
  · rintro ⟨a, ha⟩
    exact ⟨![a], by simpa using ha⟩

/-- Complement, from the hypothesis `hR` (as in the C0 hole). -/
theorem rexExistI_compl {κ : Type} [Fintype κ] {X : Set (κ → ℝ)}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ) (hX : RExpExistI X) :
    RExpExistI Xᶜ :=
  RExpExistI.compl hR hX

/-! ## 4. Countable preconnected subsets of `ℝ` are singletons -/

/-- A countable preconnected subset of `ℝ` has at most one point. -/
theorem subsingleton_of_countable_isPreconnected {s : Set ℝ} (hc : s.Countable)
    (hp : IsPreconnected s) : s.Subsingleton := by
  have hoc : s.OrdConnected := hp.ordConnected
  intro a ha b hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hsub : Set.Icc a b ⊆ s := hoc.out ha hb
    have hcnt : (Set.Icc a b).Countable := hc.mono hsub
    rw [Cardinal.Real.Icc_countable_iff] at hcnt
    exact absurd hcnt (not_le.mpr hlt)
  · have hsub : Set.Icc b a ⊆ s := hoc.out hb ha
    have hcnt : (Set.Icc b a).Countable := hc.mono hsub
    rw [Cardinal.Real.Icc_countable_iff] at hcnt
    exact absurd hcnt (not_le.mpr hlt)

end Work.WilC4aU
