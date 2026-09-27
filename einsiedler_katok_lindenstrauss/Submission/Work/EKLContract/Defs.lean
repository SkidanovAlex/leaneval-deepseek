import ChallengeDeps

/-!
# EKL contract — definitions and component `Prop`s  (FROZEN)

Formal interface for Einsiedler–Katok–Lindenstrauss,
`dimH {(α,β) | liminf n‖nα‖‖nβ‖ > 0} = 0`, following `Submission/Work/EKLPlan/Interfaces.lean`
and its companion design document `Submission/Work/EKLPlan/ROUTE_LEAD.md`.

This module is the *elaborated*, compiling version of that interface.  It was produced from the
plan file by repairing elaboration only; every deviation from the plan file is recorded in
`Submission/Work/EKLContract/NOTES.md`.  The component `Prop`s below are FROZEN: the composition
`Work.EKLContract.ekl_of_components` (in `Submission/Work/EKLContract/Glue.lean`) is proved
against exactly these statements, so any change invalidates the glue.

Conventions (ROUTE_LEAD §1):
* `G = SL₃(ℝ)`, `Γ = SL₃(ℤ)`, `X₃ = G/Γ` with a *left* action (`Pisa` uses `Γ\G` with a right
  action; translate `x.g = g⁻¹ • x`).
* Paper indices `1,2,3` are `Fin 3` indices `0,1,2`.
* "`y` is `ε`-close to `x`" always means `y = g • x` for some `g ∈ V ε` — there is no metric.
* `U_ij` is contracted by `α^t = aDiag t` iff `t i < t j`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLContract

/-! ## 1. The group, the lattice, the space of lattices -/

/-- `G = SL₃(ℝ)`. -/
abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) ℝ

/-- `Γ = SL₃(ℤ)` as a subgroup of `SL₃(ℝ)` (columns of `g` span the lattice `gℤ³`). -/
def Γ3 : Subgroup SL3 :=
  (Matrix.SpecialLinearGroup.map (n := Fin 3) (Int.castRingHom ℝ)).range

/-- `X₃ = SL₃(ℝ)/SL₃(ℤ)`, left cosets `gΓ`. -/
abbrev X3 : Type := SL3 ⧸ Γ3

instance : MeasurableSpace SL3 := borel SL3
instance : BorelSpace SL3 := ⟨rfl⟩

/-- DESIGN (as in the plan): `X₃` carries the Borel σ-algebra of the quotient topology.  The
instance is named so that it can be referred to explicitly in contexts that bind another
`MeasurableSpace X3` (Lean's typeclass search uses local hypotheses of a class type, which would
otherwise silently capture such a binder). -/
instance (priority := high) instMeasurableSpaceX3 : MeasurableSpace X3 := borel X3
instance : BorelSpace X3 := ⟨rfl⟩

/-- The projection `G → X₃`, `g ↦ gΓ`. -/
def mkX (g : SL3) : X3 := QuotientGroup.mk g

/-- Displacement neighbourhoods of the identity: max-entry distance `< δ` from `1`. -/
def V (δ : ℝ) : Set SL3 :=
  {g | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ}

/-- `x` has a nonzero lattice vector of sup-norm `< ρ` (i.e. `λ₁(x) < ρ`), stated with an
arbitrary representative. -/
def HasShortVec (x : X3) (ρ : ℝ) : Prop :=
  ∃ g : SL3, mkX g = x ∧ ∃ m : Fin 3 → ℤ, m ≠ 0 ∧
    ∀ i, |Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) ℝ) (fun j => (m j : ℝ)) i| < ρ

/-- `{λ₁ ≥ ρ}`; compact by Mahler (component C2). -/
def Thick (ρ : ℝ) : Set X3 := {x | ¬ HasShortVec x ρ}

/-! ## 2. The diagonal group `A` and the root subgroups `U_ij` -/

/-- `α^t = diag(e^{t₀-m}, e^{t₁-m}, e^{t₂-m})`, `m = (t₀+t₁+t₂)/3`.  For `∑ t = 0` this is
EKL's `α^t`; the built-in normalisation makes `aDiag` total. -/
def aDiag (t : Fin 3 → ℝ) : SL3 :=
  ⟨Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3)), by
    rw [Matrix.det_diagonal, ← Real.exp_sum Finset.univ]
    have h : (∑ i : Fin 3, (t i - (∑ j, t j) / 3)) = 0 := by
      simp only [Fin.sum_univ_three]
      ring
    rw [h, Real.exp_zero]⟩

/-- `u_ij(s) = 1 + s E_ij`. -/
def uij {i j : Fin 3} (h : i ≠ j) (s : ℝ) : SL3 := Matrix.SpecialLinearGroup.transvection h s

/-- `U_ij = {u_ij(s)}` (a subgroup; `Work.EKLContract.range_uij` identifies carrier and range). -/
def Uij {i j : Fin 3} (h : i ≠ j) : Subgroup SL3 :=
  Subgroup.closure (Set.range (fun s : ℝ => uij h s))

/-- `u_ij([-R,R])`, the ball used for leafwise measures of `U_ij`. -/
def ballU {i j : Fin 3} (h : i ≠ j) (R : ℝ) : Set SL3 := (fun s : ℝ => uij h s) '' Set.Icc (-R) R

/-- EKL's `U_(ab) = ⟨U_ab, U_ac, U_cb⟩` (`c` the third index). -/
def Upar {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) : Subgroup SL3 :=
  Uij hab ⊔ Uij hac ⊔ Uij hcb

/-- `α' = diag(e^s, e^s, e^{-2s})` with `-2s` in slot `c`: the group `A'_{ab}`. -/
def aPrime (c : Fin 3) (s : ℝ) : SL3 := aDiag (fun i => if i = c then -2 * s else s)

/-- `L_(ab) = C(U_ab)`, the centraliser of `U_ab`. -/
def Lset {a b : Fin 3} (hab : a ≠ b) : Set SL3 := {g | g * uij hab 1 = uij hab 1 * g}

/-! ## 3. The Littlewood set and the semigroup `A⁺` -/

/-- The exceptional set of the challenge, verbatim. -/
def Xi : Set (ℝ × ℝ) :=
  {(α, β) : ℝ × ℝ | Filter.atTop.liminf
      (fun n : ℕ ↦ n * distToNearestInt (n * α) * distToNearestInt (n * β)) > 0}

/-- EKL §11: `τ_{u,v} = [[1,0,0],[u,1,0],[v,0,1]] Γ`. -/
def tau (p : ℝ × ℝ) : X3 :=
  mkX (uij (show (1 : Fin 3) ≠ 0 by decide) p.1 * uij (show (2 : Fin 3) ≠ 0 by decide) p.2)

/-- `a(r,s) = diag(e^{-r-s}, e^r, e^s)`, `r,s ≥ 0` (EKL Prop 11.1). -/
def aPlus (r s : ℝ) : SL3 := aDiag ![-r - s, r, s]

/-- The expanding element `a₀ = a(1,1) = diag(e^{-2}, e, e)`. -/
def a0 : SL3 := aDiag ![-2, 1, 1]

/-- Points whose `A⁺`-orbit stays in `Thick ρ`.  Compact and `a₀`-forward-invariant. -/
def Drho (ρ : ℝ) : Set X3 := {x | ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → aPlus r s • x ∈ Thick ρ}

/-! ## 4. Separated sets ("positive topological entropy" without a metric) -/

/-- `y` is `ε`-close to `x`: the EKL metric is replaced by `V ε`, as everywhere in this file. -/
def CloseBy (ε : ℝ) (x y : X3) : Prop := ∃ g ∈ V ε, y = g • x

/-- `N`-separated set for `g` with separation `ε`. -/
def IsSeparated (g : SL3) (N : ℕ) (ε : ℝ) (E : Finset X3) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, x ≠ y → ∃ n < N, ¬ CloseBy ε ((g ^ n) • x) ((g ^ n) • y)

/-- `h_top(g|K) > 0`, phrased with separated sets (EKL §7.2). -/
def PosEnt (g : SL3) (K : Set X3) : Prop :=
  ∃ ε > 0, ∃ c > 0, ∀ N₀ : ℕ, ∃ N ≥ N₀, ∃ E : Finset X3,
    (E : Set X3) ⊆ K ∧ IsSeparated g N ε E ∧ Real.exp (c * N) ≤ (E.card : ℝ)

/-! ## 5. Kolmogorov–Sinai entropy (general measurable spaces) -/

/-- A finite measurable partition. -/
structure FinPart (X : Type*) [MeasurableSpace X] where
  n : ℕ
  parts : Fin n → Set X
  measurable : ∀ i, MeasurableSet (parts i)
  disjoint : Pairwise fun i j => Disjoint (parts i) (parts j)
  cover : ⋃ i, parts i = Set.univ

section Entropy

variable {X : Type*} [mX : MeasurableSpace X]

/-- Shannon entropy of a finite indexed family of sets. -/
def Hfam {ι : Type*} [Fintype ι] (μ : Measure X) (P : ι → Set X) : ℝ :=
  ∑ i, Real.negMulLog (μ (P i)).toReal

/-- `⋁_{k<N} T^{-k} P`, indexed by words `w : Fin N → Fin n`. -/
def joinSets (T : X → X) (P : FinPart X) (N : ℕ) : (Fin N → Fin P.n) → Set X :=
  fun w => ⋂ k : Fin N, T^[(k : ℕ)] ⁻¹' P.parts (w k)

/-- `h_μ(T,P) = inf_N (1/N) H_μ(⋁_{k<N} T^{-k}P)` (= the limit, by subadditivity). -/
def hPart (μ : Measure X) (T : X → X) (P : FinPart X) : ℝ :=
  ⨅ N : ℕ, Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1)

/-- KS entropy `h_μ(T) = sup_P h_μ(T,P) ∈ [0,∞]`.  DESIGN: valued in `ℝ≥0∞` so that
`sup` has no junk value. -/
def ent (μ : Measure X) (T : X → X) : ℝ≥0∞ :=
  ⨆ P : FinPart X, ENNReal.ofReal (hPart μ T P)

/-- The σ-algebra generated by a finite partition. -/
def partSigma (P : FinPart X) : MeasurableSpace X :=
  MeasurableSpace.generateFrom (Set.range P.parts)

/-- `Q` refines `P`. -/
def Refines (Q P : FinPart X) : Prop := ∀ i, ∃ j, Q.parts i ⊆ P.parts j

/-- Conditional entropy w.r.t. an ARBITRARY sub-σ-algebra `m` (no countable generation
needed): `H_μ(P|m) = ∫ ∑_i -E(1_{P_i}|m) log E(1_{P_i}|m) dμ`.  DESIGN: via `condExp`,
not via kernels. -/
def Hcond (μ : Measure X) (P : FinPart X) (m : MeasurableSpace X) : ℝ :=
  ∫ x, ∑ i, Real.negMulLog (condExp m μ ((@FinPart.parts X mX P i).indicator (fun _ => (1 : ℝ))) x) ∂μ

end Entropy

/-! ## 6. Invariance, ergodicity, cross-sections (leafwise-free interface notions) -/

/-- `A`-invariance. -/
def IsAInvariant (μ : Measure X3) : Prop :=
  ∀ t : Fin 3 → ℝ, MeasurePreserving (fun x : X3 => aDiag t • x) μ μ

/-- `A`-ergodic, in the strong (a.e.-invariant sets) form. -/
def IsAErgodic (μ : Measure X3) : Prop :=
  IsAInvariant μ ∧ ∀ E : Set X3, MeasurableSet E →
    (∀ t : Fin 3 → ℝ, (fun x : X3 => aDiag t • x) ⁻¹' E =ᵐ[μ] E) → μ E = 0 ∨ μ Eᶜ = 0

/-- Invariance under a subgroup `U ≤ G`. -/
def IsUInvariant (μ : Measure X3) (U : Subgroup SL3) : Prop :=
  ∀ u ∈ U, MeasurePreserving (fun x : X3 => u • x) μ μ

/-- Conull `U`-cross-section.  By Pisa 6.23 this is equivalent to "`μ_x^U` trivial a.e.". -/
def CrossSection (μ : Measure X3) (U : Subgroup SL3) : Prop :=
  ∃ B : Set X3, MeasurableSet B ∧ μ Bᶜ = 0 ∧ ∀ x ∈ B, ∀ u ∈ U, u • x ∈ B → u = 1

/-- Relative cross-section: on a conull set, `H`-translates only happen inside `L`
(EKL Lemma 4.4(1) for `H = U_(ab)`, `L = U_ab`). -/
def RelCrossSection (μ : Measure X3) (H L : Subgroup SL3) : Prop :=
  ∃ B : Set X3, MeasurableSet B ∧ μ Bᶜ = 0 ∧ ∀ x ∈ B, ∀ h ∈ H, h • x ∈ B → h ∈ L

/-! ## 7. Leafwise measures (component C5 interface) -/

/-- Admissible subgroups: closed, `A`-normalised, contracted by some `α^t`. -/
def IsHoro (U : Subgroup SL3) : Prop :=
  IsClosed (U : Set SL3) ∧
  (∀ t : Fin 3 → ℝ, ∀ u ∈ U, aDiag t * u * (aDiag t)⁻¹ ∈ U) ∧
  ∃ t : Fin 3 → ℝ, ∀ u ∈ U,
    Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)

/-- Normalising set `B₁^U`: elements of `U` with max-entry distance `≤ 1` from `1`.
For `U = U_ij` this is `u_ij([-1,1])`. -/
def Box1 (U : Subgroup SL3) : Set SL3 :=
  {g | g ∈ U ∧ ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1}

/-- Atom `[x]_m` of a σ-algebra `m`. -/
def atom (m : MeasurableSpace X3) (x : X3) : Set X3 := ⋂₀ {s | MeasurableSet[m] s ∧ x ∈ s}

/-- Shape `{u ∈ U : u • x ∈ [x]_m}`. -/
def shape (m : MeasurableSpace X3) (U : Subgroup SL3) (x : X3) : Set SL3 :=
  {u | u ∈ U ∧ u • x ∈ atom m x}

/-- `m` is a countably generated sub-σ-algebra, `Z ∈ m`, and for `x ∈ Z` the atom `[x]_m`
is an open bounded `U`-plaque inside `Z` (Pisa Def. 6.2, Thm 6.3(iv)). -/
def IsPlaqueAlgebra (U : Subgroup SL3) (Z : Set X3) (m : MeasurableSpace X3) : Prop :=
  m ≤ borel X3 ∧
  (∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b) ∧
  MeasurableSet[m] Z ∧
  ∀ x ∈ Z, atom m x ⊆ Z ∧ atom m x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) ∧
    (∃ O : Set SL3, IsOpen O ∧ shape m U x = O ∩ (U : Set SL3)) ∧
    (∃ C : ℝ, ∀ u ∈ shape m U x, ∀ i j, |u i j| ≤ C)

/-- A system of leafwise measures `x ↦ μ_x^U` (Radon measures on `SL3` carried by `U`,
normalised by `μ_x^U(B₁^U) = 1`) with co-null domain `X'`.  Fields = Pisa Thm 6.3 +
EKL §2.1 (1)–(3); the field `condexp` characterises the system uniquely a.e.

NOTE (deviation from the plan file, see NOTES.md item 3): the hypothesis on the test function
`f` is written `Measurable[instMeasurableSpaceX3] f`, i.e. measurability with respect to the
Borel σ-algebra of `X₃`.  In the plan file it was written `Measurable f` in a context that binds
another `MeasurableSpace X3`; Lean's typeclass search captures such a local hypothesis, so the
plan file silently meant `Measurable[m] f`.  The form below is the intended one (Pisa 6.3(iv)
quantifies over bounded Borel measurable `f`). -/
structure IsLeafwise (μ : Measure X3) (U : Subgroup SL3) (ν : X3 → Measure SL3) (X' : Set X3) :
    Prop where
  meas_dom : MeasurableSet X'
  conull : μ X'ᶜ = 0
  radon : ∀ x ∈ X', IsFiniteMeasureOnCompacts (ν x)
  carried : ∀ x ∈ X', ν x (U : Set SL3)ᶜ = 0
  normalised : ∀ x ∈ X', ν x (Box1 U) = 1
  measurable : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
    Measurable (fun x => ∫ g, f g ∂(ν x))
  pos : ∀ x ∈ X', ∀ δ > 0, 0 < ν x (V δ)
  equivariant : ∀ x ∈ X', ∀ u ∈ U, u • x ∈ X' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ν x = c • (ν (u • x)).map (fun g => g * u)
  condexp : ∀ (Z : Set X3) (m : MeasurableSpace X3), IsPlaqueAlgebra U Z m →
    ∀ f : X3 → ℝ, Measurable[instMeasurableSpaceX3] f → (∃ C, ∀ y, |f y| ≤ C) →
    ∀ᵐ x ∂(μ.restrict Z), condExp m (μ.restrict Z) f x =
      (∫ u in shape m U x, f (u • x) ∂(ν x)) / (ν x (shape m U x)).toReal

/-! ## 8. Component `Prop`s (FROZEN)

Each `Prop` below is a *frozen* contract: `Glue.lean` composes them into the challenge statement,
and the fleet proves them as stated.  Refereed for truth and scope; see `NOTES.md`.
-/

/-- **C1a (FROZEN)** Diophantine reduction; EKL Prop 11.1 (easy half), Pisa 12.5/12.8. -/
def P_Dioph : Prop := ∀ p ∈ Xi, ∃ ρ : ℝ, 0 < ρ ∧ tau p ∈ Drho ρ

/-- **C1b (FROZEN)** Box dimension vs. separated sets; EKL Prop 8.3 + Thm 10.1 + bookkeeping. -/
def P_BoxDim : Prop := ∀ ρ : ℝ, 0 < ρ → ¬ PosEnt a0 (Drho ρ) → dimH (tau ⁻¹' Drho ρ) = 0

/-- **C2 (FROZEN)** The space of lattices: T₂, Polish, Mahler compactness, uniform injectivity,
openness of orbit maps. -/
def P_X3 : Prop :=
  T2Space X3 ∧ PolishSpace X3 ∧
  (∀ ρ : ℝ, 0 < ρ → IsCompact (Thick ρ)) ∧
  (∀ K : Set X3, IsCompact K → ∃ δ > 0, ∀ x ∈ K, ∀ g ∈ V δ, ∀ h ∈ V δ, g • x = h • x → g = h) ∧
  (∀ x : X3, ∀ δ > 0, (fun g : SL3 => g • x) '' V δ ∈ 𝓝 x)

/-- **C3 (FROZEN)** KS entropy basics.  (E1) inverse, (E2) conjugacy, (E3) affinity,
(E4) generating sequences, (E5) conditional formula, (E6) powers, (E7) Jacobs. -/
def P_EntropyBasics : Prop :=
  ∀ {X : Type} [mX : MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ],
  (∀ T S : X → X, Measurable T → Measurable S → MeasurePreserving T μ μ →
      Function.LeftInverse S T → Function.RightInverse S T → ent μ S = ent μ T) ∧
  (∀ T φ ψ : X → X, Measurable T → Measurable φ → Measurable ψ → MeasurePreserving T μ μ →
      Function.LeftInverse ψ φ → Function.RightInverse ψ φ → (∀ x, φ (T x) = T (φ x)) →
      ent (μ.map φ) T = ent μ T) ∧
  (∀ (ν : Measure X) [IsProbabilityMeasure ν] (T : X → X) (c : ℝ≥0∞), c ≤ 1 → Measurable T →
      MeasurePreserving T μ μ → MeasurePreserving T ν ν →
      ent (c • μ + (1 - c) • ν) T = c * ent μ T + (1 - c) * ent ν T) ∧
  (∀ T : X → X, Measurable T → MeasurePreserving T μ μ → ∀ P : ℕ → FinPart X,
      (∀ m, Refines (P (m + 1)) (P m)) → (⨆ m, partSigma (P m)) = mX →
      ent μ T = ⨆ m, ENNReal.ofReal (hPart μ T (P m))) ∧
  (∀ T : X → X, Measurable T → MeasurePreserving T μ μ → ∀ P : FinPart X,
      hPart μ T P = Hcond μ P (⨆ n : ℕ, MeasurableSpace.comap (T^[n + 1]) (partSigma P))) ∧
  (∀ T : X → X, Measurable T → MeasurePreserving T μ μ → ∀ n : ℕ,
      ent μ (T^[n]) = n * ent μ T) ∧
  (∀ [StandardBorelSpace X] (T : X → X), Measurable T → MeasurePreserving T μ μ →
      ent μ T = ∫⁻ x, ent (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T ∂μ)

/-- **C4a (FROZEN)** Misiurewicz half of the variational principle. -/
def P_Misiurewicz : Prop :=
  ∀ (g : SL3) (K : Set X3), IsCompact K → (∀ x ∈ K, g • x ∈ K) → PosEnt g K →
    ∃ ν : Measure X3, IsProbabilityMeasure ν ∧ ν K = 1 ∧
      MeasurePreserving (fun x : X3 => g • x) ν ν ∧ 0 < ent ν (fun x : X3 => g • x)

/-- **C4b (FROZEN)** EKL §9: uniform finiteness and upper semicontinuity of entropy on compact
forward-invariant sets. -/
def P_USC : Prop :=
  ∀ (t : Fin 3 → ℝ) (K : Set X3), IsCompact K → (∀ x ∈ K, aDiag t • x ∈ K) →
  (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : Measure X3, IsProbabilityMeasure ν → ν K = 1 →
      MeasurePreserving (fun x : X3 => aDiag t • x) ν ν → ent ν (fun x : X3 => aDiag t • x) ≤ C) ∧
  (∀ (νseq : ℕ → Measure X3) (νlim : Measure X3), (∀ n, IsProbabilityMeasure (νseq n)) →
      IsProbabilityMeasure νlim → (∀ n, νseq n K = 1) →
      (∀ n, MeasurePreserving (fun x : X3 => aDiag t • x) (νseq n) (νseq n)) →
      (∀ f : BoundedContinuousFunction X3 ℝ,
        Tendsto (fun n => ∫ x, f x ∂(νseq n)) atTop (𝓝 (∫ x, f x ∂νlim))) →
      limsup (fun n => ent (νseq n) (fun x : X3 => aDiag t • x)) atTop ≤
        ent νlim (fun x : X3 => aDiag t • x))

/-- **C4c (FROZEN)** `A`-averaging + Bauer maximum principle ⇒ an `A`-ergodic measure. -/
def P_ErgodicMax : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ν : Measure X3, IsProbabilityMeasure ν → ν (Drho ρ) = 1 →
    MeasurePreserving (fun x : X3 => a0 • x) ν ν → 0 < ent ν (fun x : X3 => a0 • x) →
    ∃ μ : Measure X3, IsProbabilityMeasure μ ∧ IsAErgodic μ ∧ μ (Drho ρ) = 1 ∧
      0 < ent μ (fun x : X3 => a0 • x)

/-- **C4 (FROZEN)** Assembled from C2, C4a, C4c by `posEntMeasure_of` (in `Glue.lean`). -/
def P_PosEntMeasure : Prop :=
  ∀ ρ : ℝ, 0 < ρ → PosEnt a0 (Drho ρ) →
    ∃ μ : Measure X3, IsProbabilityMeasure μ ∧ IsAErgodic μ ∧ μ (Drho ρ) = 1 ∧
      0 < ent μ (fun x : X3 => a0 • x)

/-- **C5 (FROZEN)** Leafwise measures: existence, uniqueness, EKL §2.1 (4)–(9), Luzin. -/
def P_Leafwise : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ] (U : Subgroup SL3), IsHoro U →
  ∀ t0 : Fin 3 → ℝ, MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ →
    (∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1)) →
  (∃ (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ U ν X') ∧
  ∀ (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ U ν X' →
    -- (U1) uniqueness
    (∀ (ν' : X3 → Measure SL3) (X'' : Set X3), IsLeafwise μ U ν' X'' → ∀ᵐ x ∂μ, ν' x = ν x) ∧
    -- (U2) a.e. free orbits (Pisa 7.12)
    (∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) ∧
    -- (U3) trivial ⇔ cross-section (Pisa 6.23)
    (CrossSection μ U ↔ ∀ᵐ x ∂μ, ν x = Measure.dirac 1) ∧
    -- (U4) invariance ⇔ Haar (EKL (6), Pisa 6.27)
    (IsUInvariant μ U ↔ ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g => g * u) = ν x) ∧
    -- (U5) proportional ⇒ equal (EKL (8))
    (∀ᵐ x ∂μ, ∀ u ∈ U, ∀ c : ℝ≥0∞,
        (ν x).map (fun g => g * u) = c • ν x → (ν x).map (fun g => g * u) = ν x) ∧
    -- (U6) Luzin (EKL p.14, Federer 2.3.5)
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X3, IsCompact K ∧ K ⊆ X' ∧ μ Kᶜ < ε ∧
        ∀ f : CompactlySupportedContinuousMap SL3 ℝ, ContinuousOn (fun x => ∫ g, f g ∂(ν x)) K) ∧
    -- (U7) A-covariance on a single co-null set (EKL (4)); c = 1 when `aDiag t` centralises U
    (IsAInvariant μ → ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
        ∀ (t : Fin 3 → ℝ) (x : X3), x ∈ X'' → aDiag t • x ∈ X'' →
          ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (aDiag t • x) = c • (ν x).map (fun g => aDiag t * g * (aDiag t)⁻¹)) ∧
    -- (U8) ergodic dichotomy: trivial a.e. or no atom at the identity a.e.
    (IsAErgodic μ → CrossSection μ U ∨ ∀ᵐ x ∂μ, ν x {1} = 0) ∧
    -- (U9) EKL (9) for one-dimensional root groups
    (IsAErgodic μ → ∀ (i j : Fin 3) (hij : i ≠ j), U = Uij hij →
        ¬ (∀ᵐ x ∂μ, ∀ s : ℝ, s ≠ 0 → (ν x).map (fun g => g * uij hij s) ≠ ν x) →
        IsUInvariant μ U)

/-- **C5b (FROZEN)** Product structure; Pisa Prop 8.5 / Cor 8.8, in test-function form. -/
def P_Product : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
  ∀ (H T U : Subgroup SL3), IsHoro H → IsHoro T → IsHoro U → T ≤ H → U ≤ H →
  (∃ t : Fin 3 → ℝ, (∀ g ∈ T, aDiag t * g = g * aDiag t) ∧
      ∀ u ∈ U, Tendsto (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (𝓝 1)) →
  (∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) →
  (∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) →
  (∀ g ∈ T, g ∈ U → g = 1) →
  ∀ (νH νT νU : X3 → Measure SL3) (XH XT XU : Set X3),
    IsLeafwise μ H νH XH → IsLeafwise μ T νT XT → IsLeafwise μ U νU XU →
    ∀ᵐ x ∂μ, ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(νH x) = c * ∫ g, (∫ u, f (g * u) ∂(νU x)) ∂(νT x)

/-- **C6 (FROZEN)** Entropy ↔ leafwise measures; Pisa Thm 7.6 + Cor 8.8, EKL (7).
`U_ij` is contracted by `α^t` iff `t i < t j`. -/
def P_EntropyLeaf : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAErgodic μ → ∀ t : Fin 3 → ℝ,
    (0 < ent μ (fun x : X3 => aDiag t • x) ↔
      ∃ (i j : Fin 3) (hij : i ≠ j), t i < t j ∧ ¬ CrossSection μ (Uij hij))

/-- **C6b (FROZEN)** EKL Lemma 4.4(1). -/
def P_RelCross : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAErgodic μ →
  ∀ (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b),
    CrossSection μ (Uij hac) → CrossSection μ (Uij hcb) →
    RelCrossSection μ (Upar hab hac hcb) (Uij hab)

/-- **C7 (FROZEN)** EKL Lemma 3.3 = Einsiedler–Katok Lemma 6.1; Pisa 9.11. -/
def P_Commutator : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAErgodic μ →
  ∀ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
    ¬ CrossSection μ (Uij hij) → ¬ CrossSection μ (Uij hjk) → IsUInvariant μ (Uij hik)

/-- Non-exceptional `A'_{ab}`-returns to every positive-measure compact set avoiding `N`
(the negation of EKL Def. 4.1 "exceptional", with EKL Lemma 4.2's null set built in). -/
def NonExceptional (μ : Measure X3) {a b : Fin 3} (hab : a ≠ b) (c : Fin 3) : Prop :=
  ∃ N : Set X3, μ N = 0 ∧ ∀ K : Set X3, IsCompact K → Disjoint K N → 0 < μ K →
    ∀ δ : ℝ, 0 < δ → ∃ z ∈ K, ∃ s : ℝ, ∃ g ∈ V δ,
      aPrime c s • z ∈ K ∧ aPrime c s • z = g • z ∧ g ∉ Lset hab

/-- **C9 (FROZEN)** EKL Lemma 4.2 + §5, specialised: no exceptional returns for `SL₃(ℤ)`. -/
def P_NonExc : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
  ∀ (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b), NonExceptional μ hab c

/-- **C8 (FROZEN)** EKL §4.2–4.5: the low entropy method. -/
def P_LowEntropyCore : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAErgodic μ →
  ∀ (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b),
    RelCrossSection μ (Upar hab hac hcb) (Uij hab) → ¬ CrossSection μ (Uij hab) →
    NonExceptional μ hab c → IsUInvariant μ (Uij hab)

/-- **Low entropy theorem (FROZEN)** for `SL₃(ℤ)`, assembled by `lowEntropy_of`. -/
def P_LowEntropy : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAErgodic μ →
  ∀ (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b),
    ¬ CrossSection μ (Uij hab) → CrossSection μ (Uij hac) → CrossSection μ (Uij hcb) →
    IsUInvariant μ (Uij hab)

/-- **C10 (FROZEN)** Endgame, replaces EKL §6 / Ratner. -/
def P_Endgame : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
  ∀ (i j : Fin 3) (hij : i ≠ j), IsUInvariant μ (Uij hij) → ∀ ρ : ℝ, 0 < ρ → μ (Thick ρ) ≠ 1

/-- **C11a (FROZEN)** Lindenstrauss–Rudolph maximal inequality for leafwise measures, EKL (10). -/
def P_MaxLeaf : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
  ∀ (i j : Fin 3) (hij : i ≠ j) (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ (Uij hij) ν X' →
  ∀ f : X3 → ℝ, Measurable f → (∀ x, 0 ≤ f x) → Integrable f μ → ∀ α : ℝ, 0 < α →
    μ {x | x ∈ X' ∧ ∃ r : ℝ, 0 < r ∧
        α * (ν x (ballU hij r)).toReal < ∫ g in ballU hij r, f (g • x) ∂(ν x)}
      ≤ ENNReal.ofReal (C * (∫ x, f x ∂μ) / α)

/-- **C11b (FROZEN)** Maximal inequality for the one-parameter flows `τ ↦ α^{τ t}`. -/
def P_MaxFlow : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
  ∀ (t : Fin 3 → ℝ) (f : X3 → ℝ), Measurable f → (∀ x, 0 ≤ f x) → Integrable f μ →
  ∀ α : ℝ, 0 < α →
    μ {x | ∃ T : ℝ, 0 < T ∧ α * T < ∫ τ in (0 : ℝ)..T, f (aDiag (τ • t) • x)}
      ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / α)

/-- **C11c (FROZEN)** Birkhoff pointwise ergodic theorem. -/
def P_Birkhoff : Prop :=
  ∀ {X : Type} [mX : MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X),
    MeasurePreserving T μ μ → ∀ f : X → ℝ, Integrable f μ →
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x)) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ f x))

end Work.EKLContract
