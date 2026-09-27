import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC8Core.phi_conj_u
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.Box1_Uij
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.aDiag_conj_uij

/-!
# C8 — definitions of the low-entropy assembly

Vocabulary for the assembly of EKL §4.2–4.5 (`Work.EKLContract.P_LowEntropyCore`):
`u r = u_01(r)`, the contracting flow `phi`, the parameter `par` of `U_01` and the
`ℝ`-valued leafwise measure `nuR`.

Vocabulary fixed here:

* `u r = u_01(r)`, the shearing unipotent (paper `u_12(r)`);
* `phi τ = α^{-τ(-1,1,0)} = diag(e^{-τ}, e^{τ}, 1)`, the contracting flow;
* `par g = g_{01}`, the parameter of `U_01`, a continuous retraction of `SL₃` onto `ℝ`
  restricting to the inverse of `s ↦ u_01(s)` on `U_01`;
* `nuR ν = (ν.restrict U_01).map par`, the `ℝ`-valued leafwise measure (`ν_x^ℝ`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract

noncomputable section

namespace Work.EKLComp

/-! ## 1. The distinguished configuration `(a,b,c) = (0,1,2)` -/

abbrev h01 : (0 : Fin 3) ≠ 1 := by decide
abbrev h02 : (0 : Fin 3) ≠ 2 := by decide
abbrev h21 : (2 : Fin 3) ≠ 1 := by decide

/-- `u(r) = u_01(r)`. -/
def u (r : ℝ) : SL3 := uij h01 r

/-- The contracting flow `φ_τ = α^{-τ(-1,1,0)} = diag(e^{-τ}, e^{τ}, 1)`. -/
def phi (τ : ℝ) : SL3 := aDiag (τ • ![(-1 : ℝ), 1, 0])

/-- The parameter of `U_01`, read off as the `(0,1)`-entry. -/
def par (g : SL3) : ℝ := (g : Matrix (Fin 3) (Fin 3) ℝ) 0 1

/-- The `ℝ`-valued leafwise measure: restrict to `U_01` and read off the parameter. -/
def nuR (ν : Measure SL3) : Measure ℝ := (ν.restrict (Uij h01 : Set SL3)).map par

/-! ## 2. `U_01` and its parameter -/

theorem continuous_par : Continuous par := by
  have h : Continuous fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) := continuous_subtype_val
  exact (continuous_apply 1).comp ((continuous_apply 0).comp h)

theorem measurable_par : Measurable par := continuous_par.measurable

theorem par_uij_h01 (s : ℝ) : par (uij h01 s) = s := by
  show ((uij h01 s : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = s
  exact Work.EKLContract.Lemmas.uij_apply_self h01 s

theorem par_u (s : ℝ) : par (u s) = s := par_uij_h01 s

theorem par_one : par 1 = 0 := by
  show ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne h01]

theorem uij_h01_mul (s t : ℝ) : uij h01 s * uij h01 t = uij h01 (s + t) :=
  (Matrix.SpecialLinearGroup.transvection_add h01 s t).symm

theorem u_mul (s t : ℝ) : u s * u t = u (s + t) := uij_h01_mul s t

theorem u_zero : u 0 = 1 := Matrix.SpecialLinearGroup.transvection_coeff_zero h01

theorem u_inv (s : ℝ) : (u s)⁻¹ = u (-s) := Matrix.SpecialLinearGroup.transvection_inv h01 s

theorem u_mem (s : ℝ) : u s ∈ (Uij h01 : Set SL3) := Subgroup.subset_closure ⟨s, rfl⟩

theorem u_ne_one {s : ℝ} (hs : s ≠ 0) : u s ≠ 1 := by
  intro h
  have h' := congrArg par h
  rw [par_u s, par_one] at h'
  exact hs h'

/-- `par` is additive along right multiplication by `u(s)`, on `U_01`. -/
theorem par_mul_u {g : SL3} (hg : g ∈ (Uij h01 : Set SL3)) (s : ℝ) :
    par (g * u s) = par g + s := by
  obtain ⟨t, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff h01 g).mp hg
  have h1 : uij h01 t * u s = uij h01 (t + s) := by
    rw [show u s = uij h01 s from rfl, uij_h01_mul]
  rw [h1, par_uij_h01, par_uij_h01]

theorem par_phi_conj_u (τ r : ℝ) : par (phi τ * u r * (phi τ)⁻¹) = Real.exp (-2 * τ) * r := by
  have h : phi τ * u r * (phi τ)⁻¹ = u (Real.exp (-2 * τ) * r) :=
    Work.EKLC8Core.phi_conj_u τ r
  rw [h, par_u]

/-! ## 3. The `ℝ`-valued leafwise measure `nuR` -/

theorem isCompact_ballU (R : ℝ) : IsCompact (ballU h01 R) :=
  isCompact_Icc.image (Work.EKLContract.Lemmas.horoUij_cont h01)

theorem closed_Uij : IsClosed (Uij h01 : Set SL3) := Work.EKLContract.Lemmas.horoUij_isClosed h01

theorem par_preimage_Icc (R : ℝ) :
    (Uij h01 : Set SL3) ∩ par ⁻¹' Set.Icc (-R) R = ballU h01 R := by
  ext g
  constructor
  · intro hg
    obtain ⟨hU, hp⟩ := hg
    obtain ⟨t, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff h01 g).mp hU
    simp only [Set.mem_preimage] at hp
    rw [par_uij_h01] at hp
    exact ⟨t, hp, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Subgroup.subset_closure ⟨t, rfl⟩, ?_⟩
    simp only [Set.mem_preimage]
    rwa [par_uij_h01]

theorem nuR_Icc (ν : Measure SL3) (R : ℝ) :
    nuR ν (Set.Icc (-R) R) = ν (ballU h01 R) := by
  have h1 : nuR ν (Set.Icc (-R) R)
      = (ν.restrict (Uij h01 : Set SL3)) (par ⁻¹' Set.Icc (-R) R) :=
    Measure.map_apply measurable_par measurableSet_Icc
  rw [h1, Measure.restrict_apply (measurable_par measurableSet_Icc), Set.inter_comm,
    par_preimage_Icc R]

theorem nuR_finite {ν : Measure SL3} (hν : IsFiniteMeasureOnCompacts ν) (R : ℝ) :
    nuR ν (Set.Icc (-R) R) ≠ ⊤ := by
  rw [nuR_Icc]
  exact (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := ν) (isCompact_ballU R)).ne

theorem nuR_normalised {ν : Measure SL3} (hν : ν (Box1 (Uij h01)) = 1) :
    nuR ν (Set.Icc (-1) 1) = 1 := by
  rw [nuR_Icc, ← Work.EKLContract.Lemmas.Box1_Uij h01]
  exact hν

theorem nuR_smul (c : ℝ≥0∞) (ν : Measure SL3) : nuR (c • ν) = c • nuR ν := by
  show ((c • ν).restrict (Uij h01 : Set SL3)).map par
    = c • ((ν.restrict (Uij h01 : Set SL3)).map par)
  rw [Measure.restrict_smul, Measure.map_smul _ continuous_par.measurable.aemeasurable]

theorem ae_mem_Uij_of_compl_eq_zero {ν : Measure SL3} (hν : ν (Uij h01 : Set SL3)ᶜ = 0) :
    ∀ᵐ g ∂ν, g ∈ (Uij h01 : Set SL3) := by
  rw [MeasureTheory.ae_iff]
  show ν (Uij h01 : Set SL3)ᶜ = 0
  exact hν

theorem restrict_Uij_of_compl_eq_zero {ν : Measure SL3}
    (hν : ν (Uij h01 : Set SL3)ᶜ = 0) : ν.restrict (Uij h01 : Set SL3) = ν :=
  Measure.restrict_eq_self_of_ae_mem (ae_mem_Uij_of_compl_eq_zero hν)

/-- Right multiplication by `u(s)` shifts the parameter of the `ℝ`-valued leafwise measure by
`s` (EKL (3) at the level of `nuR`). -/
theorem nuR_map_mul_u {ν : Measure SL3} (hν : ν (Uij h01 : Set SL3)ᶜ = 0) (s : ℝ) :
    nuR (ν.map (fun g => g * u s)) = (nuR ν).map (fun t => t + s) := by
  have hf : Measurable (fun g : SL3 => g * u s) := (continuous_mul_const (u s)).measurable
  have hcar : (ν.map (fun g : SL3 => g * u s)) (Uij h01 : Set SL3)ᶜ = 0 := by
    rw [Measure.map_apply hf (closed_Uij.measurableSet.compl)]
    refine measure_mono_null (fun g hg => ?_) hν
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hg ⊢
    exact fun hgU => hg (mul_mem hgU (u_mem s))
  have h0 : ν.restrict (Uij h01 : Set SL3) = ν := restrict_Uij_of_compl_eq_zero hν
  have h1 : (ν.map (fun g : SL3 => g * u s)).restrict (Uij h01 : Set SL3)
      = ν.map (fun g : SL3 => g * u s) := restrict_Uij_of_compl_eq_zero hcar
  have hfun : (fun g : SL3 => par (g * u s)) =ᵐ[ν] (fun g : SL3 => par g + s) := by
    filter_upwards [ae_mem_Uij_of_compl_eq_zero hν] with g hg
    exact par_mul_u hg s
  rw [nuR, h1, nuR, h0,
    Measure.map_map (g := par) (f := fun g : SL3 => g * u s) measurable_par hf,
    Measure.map_map (g := fun t : ℝ => t + s) (f := par) (measurable_id.add_const s)
      measurable_par]
  exact Measure.map_congr hfun

/-! ## 3bis. The clauses of `P_Leafwise` consumed by the assembly

`P_Leafwise`'s conclusions for `U = Uij h01` are packaged as four `Prop`s, so that the
assembly (and the delegated pieces of it) can take exactly the clauses they use. -/

/-- The flow `Φ_τ x = α^{-τ(-1,1,0)} • x`. -/
def Phi (τ : ℝ) (x : X3) : X3 := phi τ • x

/-- EKL (8) = (U5) of `P_Leafwise`, at `U = Uij h01`. -/
def U5clause (μ : Measure X3) (ν : X3 → Measure SL3) : Prop :=
  ∀ᵐ x ∂μ, ∀ u ∈ (Uij h01 : Set SL3), ∀ c : ℝ≥0∞,
    (ν x).map (fun g => g * u) = c • ν x → (ν x).map (fun g => g * u) = ν x

/-- (U6) of `P_Leafwise` (Luzin) at `U = Uij h01`, domain `X'`. -/
def U6clause (μ : Measure X3) (ν : X3 → Measure SL3) (X' : Set X3) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X3, IsCompact K ∧ K ⊆ X' ∧ μ Kᶜ < ε ∧
    ∀ f : CompactlySupportedContinuousMap SL3 ℝ, ContinuousOn (fun x => ∫ g, f g ∂(ν x)) K

/-- (U7) of `P_Leafwise` (`A`-covariance) at `U = Uij h01`, domain `X'`. -/
def U7clause (μ : Measure X3) (ν : X3 → Measure SL3) (X' : Set X3) : Prop :=
  ∃ X'' : Set X3, X'' ⊆ X' ∧ MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
    ∀ (t : Fin 3 → ℝ) (x : X3), x ∈ X'' → aDiag t • x ∈ X'' →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (aDiag t • x) = c • (ν x).map (fun g => aDiag t * g * (aDiag t)⁻¹)

/-- (U9) of `P_Leafwise` (EKL (9)) at `U = Uij h01`. -/
def U9clause (μ : Measure X3) (ν : X3 → Measure SL3) : Prop :=
  IsAErgodic μ →
    ¬ (∀ᵐ x ∂μ, ∀ s : ℝ, s ≠ 0 → (ν x).map (fun g => g * uij h01 s) ≠ ν x) →
    IsUInvariant μ (Uij h01)

/-- The leafwise system made finite on compacts *everywhere*: outside the domain `X'` it is
replaced by the Dirac mass at the identity.  (`IsLeafwise` only constrains `ν x` for `x ∈ X'`,
which is not enough for a global measurability statement; `fixRadon` is the harmless
normalisation that removes this degeneracy.) -/
noncomputable def fixRadon (ν : X3 → Measure SL3) (X' : Set X3) : X3 → Measure SL3 :=
  fun x => by classical exact if x ∈ X' then ν x else Measure.dirac (1 : SL3)

theorem fixRadon_of_mem {ν : X3 → Measure SL3} {X' : Set X3} {x : X3} (hx : x ∈ X') :
    fixRadon ν X' x = ν x := by classical exact if_pos hx

theorem fixRadon_of_notMem {ν : X3 → Measure SL3} {X' : Set X3} {x : X3} (hx : x ∉ X') :
    fixRadon ν X' x = Measure.dirac (1 : SL3) := by classical exact if_neg hx

theorem isFiniteMeasureOnCompacts_dirac (a : SL3) : IsFiniteMeasureOnCompacts (Measure.dirac a) :=
  inferInstance

/-! ## 4. The data of the low-entropy argument

`C8Setup μ` bundles everything the assembly of EKL §4.2–4.5 (`ROUTE_LEAD.md` §5, Steps 1–11)
produces before the final contradiction: the leafwise system with the clauses (U5)–(U9) it
consumes, the constants `ε, ρ`, the Luzin compact `X₁`, the maximal-inequality set `X₂`, the
set `𝒳(ρ)`, the flow-averaging compact `X₃`, and the null set `N` of exceptional points.

The two constructions are isolated:

* `C8Setup.exists_of` (to be proved): `P_X3 → P_Leafwise → P_MaxLeaf → P_MaxFlow` and the
  hypotheses of `P_LowEntropyCore` produce a `C8Setup μ` (Steps 1–4);
* `C8Setup.limit_pair` (to be proved): a `C8Setup μ` plus `NonExceptional μ h01 2` produces
  `y, y' ∈ X₁` with `y' = h • y` for some `h ∈ U_(01)`, `h ≠ 1`, and `ν y = ν y'`
  (Steps 6–11).
-/

/-- The mass of the plaque of radius `R` through `x` that lies in `S`
(`= ν_x (ballU R ∩ {g | g • x ∈ S})`). -/
def leafMass (ν : X3 → Measure SL3) (S : Set X3) (R : ℝ) (x : X3) : ℝ≥0∞ :=
  ∫⁻ g in ballU h01 R, Set.indicator S (fun _ => (1 : ℝ≥0∞)) (g • x) ∂(ν x)

/-- The data of Steps 1–6 of the low-entropy argument. -/
structure C8Setup (μ : Measure X3) where
  /-- the leafwise system for `U_01`, finite on compacts everywhere -/
  ν : X3 → Measure SL3
  X' : Set X3
  lw : IsLeafwise μ (Uij h01) ν X'
  radon : ∀ x, IsFiniteMeasureOnCompacts (ν x)
  norm : ∀ x, (nuR (ν x)).real (Set.Icc (-1) 1) = 1
  /-- the conull `A`-covariance set (U7) and its consequences -/
  X'' : Set X3
  X''_sub : X'' ⊆ X'
  X''_conull : μ X''ᶜ = 0
  scale : ∀ x ∈ X'', ∀ w σ : ℝ, phi w • x ∈ X'' →
    (nuR (ν (phi w • x))).real (Set.Icc (-σ) σ)
        * (nuR (ν x)).real (Set.Icc (-(Real.exp (2 * w))) (Real.exp (2 * w)))
      = (nuR (ν x)).real (Set.Icc (-(σ * Real.exp (2 * w))) (σ * Real.exp (2 * w)))
        * (nuR (ν (phi w • x))).real (Set.Icc (-1) 1)
  central : ∀ x ∈ X'', ∀ s : ℝ, aPrime 2 s • x ∈ X'' → ν (aPrime 2 s • x) = ν x
  /-- (U9) contrapositive (Step 0) and (U8) (no atom at the identity) on `X''` -/
  nontriv : ∀ x ∈ X'', ∀ s : ℝ, s ≠ 0 → u s • x ∈ X'' → ν (u s • x) ≠ ν x
  noAtom : ∀ x ∈ X'', (nuR (ν x)) {0} = 0
  /-- (F4): equality of leafwise measures is preserved by translating with `u s` -/
  transfer : ∀ x ∈ X'', ∀ x' ∈ X'', ∀ s : ℝ, u s • x ∈ X'' → u s • x' ∈ X'' →
    nuR (ν x) = nuR (ν x') → nuR (ν (u s • x)) = nuR (ν (u s • x'))
  /-- the constants -/
  ε : ℝ
  ε_pos : 0 < ε
  ε_small : ε ≤ 1 / 100
  ρ : ℝ
  ρ_pos : 0 < ρ
  ρ_small : ρ ≤ 1 / 2
  C : ℝ
  C_pos : 0 < C
  C_ge_one : 1 ≤ C
  ε_small_C : (C + 2) * ε ≤ 1 / 4
  /-- the conull set of the relative cross-section hypothesis and the null set of
  exceptional points -/
  B : Set X3
  B_meas : MeasurableSet B
  B_conull : μ Bᶜ = 0
  B_rel : ∀ x ∈ B, ∀ h ∈ (Upar h01 h02 h21 : Set SL3), h • x ∈ B → h ∈ (Uij h01 : Set SL3)
  N : Set X3
  N_null : μ N = 0
  /-- the Luzin compact `X₁` -/
  X₁ : Set X3
  X₁_compact : IsCompact X₁
  X₁_sub : X₁ ⊆ X'' ∩ B
  X₁_meas : 1 - ε ^ 4 < (μ X₁).toReal
  X₁_cont : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
    ContinuousOn (fun x => ∫ g, f g ∂(ν x)) X₁
  X₁_limit : ∀ (y y' : X3) (ys ys' : ℕ → X3), (∀ n, ys n ∈ X₁) → (∀ n, ys' n ∈ X₁) →
    Tendsto ys atTop (𝓝 y) → Tendsto ys' atTop (𝓝 y') →
    (∀ n, ν (ys n) = ν (ys' n)) → ν y = ν y'
  /-- the maximal-inequality set `X₂` (density one along the `U_01`-leaves) -/
  X₂ : Set X3
  X₂_def : ∀ x, x ∈ X₂ ↔ x ∈ X'' ∧ ∀ R : ℝ, 0 < R →
    (1 - ε ^ 2) * (ν x (ballU h01 R)).toReal ≤ (leafMass ν X₁ R x).toReal
  X₂_meas_set : MeasurableSet X₂
  X₂_meas : 1 - C * ε ^ 2 ≤ (μ X₂).toReal
  /-- EKL's `𝒳(ρ)` -/
  Xrho : Set X3
  Xrho_def : ∀ x, x ∈ Xrho ↔ x ∈ X'' ∧ (nuR (ν x)).real (Set.Icc (-ρ) ρ) < (1 / 2 : ℝ)
  Xrho_meas_set : MeasurableSet Xrho
  Xrho_meas : 1 - ε ^ 2 < (μ Xrho).toReal
  /-- the flow-averaging compact `X₃` -/
  X₃ : Set X3
  X₃_compact : IsCompact X₃
  X₃_sub : X₃ ⊆ X'' ∩ Nᶜ
  X₃_meas : 1 - (C + 2) * ε < (μ X₃).toReal
  X₃_avg₁ : ∀ x ∈ X₃, ∀ T : ℝ, 0 < T →
    (1 - ε) * T ≤ ∫ τ in (0 : ℝ)..T, Set.indicator X₂ (fun _ => (1 : ℝ)) (Phi τ x)
  X₃_avg₂ : ∀ x ∈ X₃, ∀ T : ℝ, 0 < T →
    (1 - ε) * T ≤ ∫ τ in (0 : ℝ)..T, Set.indicator Xrho (fun _ => (1 : ℝ)) (Phi τ x)

end Work.EKLComp
