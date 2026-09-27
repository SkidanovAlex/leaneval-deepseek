import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.aDiag_conj_uij
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# C7 (commutator lemma): definitions

Vocabulary for component C7 of the frozen EKL contract, `Work.EKLContract.P_Commutator`
(EKL Lemma 3.3 = Einsiedler–Katok Lemma 6.1; Pisa 9.11, ROUTE_LEAD §C7).

For distinct indices `i, j, k : Fin 3` the three root groups `U_ij`, `U_jk`, `U_ik` span a
three-step-free (2-step) nilpotent group, the Heisenberg group `Heis3 = ⟨U_ij, U_jk, U_ik⟩`,
in which `U_ik` is the centre and `[u_ij(p), u_jk(r)] = u_ik(p r)`.  The parametrisation

`heis p q r = u_ij(p) · u_jk(r) · u_ik(q - p r)`

is the element `1 + p E_ij + q E_ik + r E_jk` of `SL₃(ℝ)`; it is bijective onto `Heis3` and its
multiplication is `(p,q,r)(p',q',r') = (p+p', q+q'+p r', r+r')` (a lemma, in `HeisLaw.lean`).

The two *abelian* subgroups `VijIk = U_ij ⊔ U_ik` and `VjkIk = U_jk ⊔ U_ik` are the two
"opposite" complements of `U_jk` resp. `U_ij` inside `Heis3`; C7 decomposes `Heis3` in the two
orders `Heis3 = U_ij ⋉ VjkIk` and `Heis3 = U_jk ⋉ VijIk` and compares the corresponding
product formulas (Pisa 9.11).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.EKLC7

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-- The Heisenberg element `1 + p E_ij + q E_ik + r E_jk`, written as a product of root-group
elements: `u_ij(p) · u_jk(r) · u_ik(q - p r)`.  (For `u_ij(p) u_jk(r) = 1 + pE_ij + rE_jk +
p r E_ik`.) -/
def heis {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : ℝ) : SL3 :=
  uij hij p * uij hjk r * uij hik (q - p * r)

/-- The Heisenberg group `⟨U_ij, U_jk, U_ik⟩ = U_ij ⊔ U_jk ⊔ U_ik` spanned by the three root
groups of a triple of distinct indices.  Its centre is `U_ik`. -/
def Heis3 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) : Subgroup SL3 :=
  Uij hij ⊔ Uij hjk ⊔ Uij hik

/-- The abelian subgroup `U_jk ⊔ U_ik` (the complement of `U_ij` in `Heis3`). -/
def VjkIk {i j k : Fin 3} (hjk : j ≠ k) (hik : i ≠ k) : Subgroup SL3 :=
  Uij hjk ⊔ Uij hik

/-- The abelian subgroup `U_ij ⊔ U_ik` (the complement of `U_jk` in `Heis3`). -/
def VijIk {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) : Subgroup SL3 :=
  Uij hij ⊔ Uij hik

/-! ## Elementary facts about `heis` -/

/-- `heis 0 0 0 = 1`. -/
theorem heis_zero {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    heis hij hjk hik 0 0 0 = 1 := by
  simp [heis, uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]

/-- Every `heis p q r` lies in the Heisenberg group `Heis3`. -/
theorem heis_mem {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : ℝ) :
    heis hij hjk hik p q r ∈ Heis3 hij hjk hik := by
  rw [heis, Heis3]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.subset_closure ⟨p, rfl⟩)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨r, rfl⟩))))
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨q - p * r, rfl⟩))

/-- `u_ik q` as a Heisenberg element. -/
theorem heis_uik {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (q : ℝ) :
    heis hij hjk hik 0 q 0 = uij hik q := by
  simp [heis, uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]

/-- `u_ij p` as a Heisenberg element. -/
theorem heis_uij {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p : ℝ) :
    heis hij hjk hik p 0 0 = uij hij p := by
  simp [heis, uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]

/-- `u_jk r` as a Heisenberg element. -/
theorem heis_ujk {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (r : ℝ) :
    heis hij hjk hik 0 0 r = uij hjk r := by
  simp [heis, uij, Matrix.SpecialLinearGroup.transvection_coeff_zero]


/-! ## The three product formulae for the Heisenberg leafwise measure

`TripleA` and `TripleB` are the two ways (Pisa 9.11, the two "allowed orders" of the coarse
Lyapunov weights) of writing the leafwise measure `νN` of the Heisenberg group as the image of
the product of the three one-dimensional leafwise measures `νij`, `νjk`, `νik` under the product
map `(g₁,g₂,g₃) ↦ g₁g₂g₃`:

* `TripleA` attaches `νij` to the outer, `νjk` to the middle and `νik` to the inner variable
  (the order `U_ij · U_jk · U_ik`), so that the integrated element is `g_ij · g_jk · g_ik`;
* `TripleB` attaches `νjk` to the outer, `νij` to the middle and `νik` to the inner variable
  (the order `U_jk · U_ij · U_ik`), so that the integrated element is `g_jk · g_ij · g_ik`.

Since `u_jk(r) u_ij(p) = u_ik(-p r) u_ij(p) u_jk(r)` the two integrands differ by the central
translation `u_ik(-p r)`, and comparing the two formulae is what produces the commutator
translation of `νik` (the heart of C7). -/

/-- The `U_ij · U_jk · U_ik` product formula for the Heisenberg leafwise measure. -/
def TripleA (νN νij νjk νik : Measure SL3) (c : ℝ) : Prop :=
  ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
    ∫ g, f g ∂νN = c * ∫ g₁, ∫ g₂, ∫ g₃, f (g₁ * g₂ * g₃) ∂νik ∂νjk ∂νij

/-- The `U_jk · U_ij · U_ik` product formula for the Heisenberg leafwise measure. -/
def TripleB (νN νij νjk νik : Measure SL3) (c : ℝ) : Prop :=
  ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
    ∫ g, f g ∂νN = c * ∫ g₁, ∫ g₂, ∫ g₃, f (g₁ * g₂ * g₃) ∂νik ∂νij ∂νjk

/-! ## Matrix-entry coordinates

The `(i,j)`-, `(i,k)`- and `(j,k)`-matrix entries are the coordinates `p`, `q`, `r` of the
Heisenberg parametrisation `heis p q r = 1 + p E_ij + q E_ik + r E_jk`; on the root group `U_ij`
the rank-one entry `(i,j)` is the parameter of the transvection.  These entries are *continuous*
functions of the group element, which is what makes them usable for pushing measures forward
(unlike a `Classical.choose`-based coordinate, whose measurability is not available). -/

/-- The `(i,j)`-entry, the coordinate `p` of `heis p q r`. -/
def pcoord (i j : Fin 3) (g : SL3) : ℝ := g i j

/-- The `(i,k)`-entry, the coordinate `q` of `heis p q r`. -/
def qcoord (i k : Fin 3) (g : SL3) : ℝ := g i k

/-- The `(j,k)`-entry, the coordinate `r` of `heis p q r`. -/
def rcoord (j k : Fin 3) (g : SL3) : ℝ := g j k

theorem continuous_entry (a b : Fin 3) :
    Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => A a b) :=
  (continuous_apply b).comp (continuous_apply a)

theorem continuous_pcoord (i j : Fin 3) : Continuous (pcoord i j) :=
  (continuous_entry i j).comp continuous_subtype_val

theorem continuous_qcoord (i k : Fin 3) : Continuous (qcoord i k) :=
  (continuous_entry i k).comp continuous_subtype_val

theorem continuous_rcoord (j k : Fin 3) : Continuous (rcoord j k) :=
  (continuous_entry j k).comp continuous_subtype_val


/-! ## The C7 interface: the two halves of the leafwise-measure input

C7 (EKL Lemma 3.3) is proved from `P_Leafwise` and `P_Product`.  For the assembly it is
convenient to split off exactly the two consequences of `P_Leafwise` that the commutator
argument uses:

* `P_LeafwiseEx` — the *existence* half of `P_Leafwise` (Pisa Thm 6.3): every horospherical
  subgroup of an `A`-invariant probability measure carries a system of leafwise measures;
* `P_RootProps` — clauses (U4) (`U`-invariance ⇔ a.e. Haar leafwise measures) and (U5)
  (proportional ⇒ equal) of `P_Leafwise`, restricted to the one-dimensional root groups
  `U_ij`, which is where C7 applies them.

Both are immediate consequences of the frozen `P_Leafwise` (its first conjunct, and its second
conjunct at `U = Uij hij`), and both are stated for the notions of `EKLContract/Defs.lean`. -/

/-- The commutator `a * b * a⁻¹ * b⁻¹` of two elements of `SL₃(ℝ)`. -/
def comm (a b : SL3) : SL3 := a * b * a⁻¹ * b⁻¹

/-- The type of the leafwise measures: Radon measures on the ambient group `SL₃(ℝ)`. -/
abbrev SLm : Type := Measure SL3

/-- `ν` is invariant under right translation by arbitrarily small non-trivial elements
`u_ij(τ)` of the root group `U_ij`. -/
def SmallPeriods {i j : Fin 3} (hij : i ≠ j) (ν : SLm) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, τ ≠ 0 ∧ |τ| ≤ ε ∧ ν.map (fun g => g * uij hij τ) = ν

/-- The a.e. commutator-translation identity for the triple of leafwise measures of a
Heisenberg configuration: right translation of `νik` by the commutator `[z.1, z.2]` multiplies
it by `c`, for `(νij ⊗ νjk)`-a.e. `z`. -/
def CommRel (νij νjk νik : SLm) (c : ℝ) : Prop :=
  ∀ᵐ z ∂(νij.prod νjk), (νik).map (fun g => g * comm z.1 z.2) = ENNReal.ofReal c • νik

/-- The *iterated* (Fubini-free) form of `CommRel`: the commutator-translation identity holds
for `νij`-a.e. first variable and, for each such, `νjk`-a.e. second variable.

This form avoids `Measure.prod`, which in the pinned Mathlib is *defined* to be `0` when the
slice kernel `x ↦ Measure.map (Prod.mk x) νjk` is not a.e.-measurable; with the iterated form the
statement is meaningful for every pair of Radon measures, which is what the commutator argument
needs. -/
def CommRel2 (νij νjk νik : SLm) (c : ℝ) : Prop :=
  ∀ᵐ x ∂νij, ∀ᵐ y ∂νjk, (νik).map (fun g => g * comm x y) = ENNReal.ofReal c • νik

/-- The existence half of `P_Leafwise`: for every `A`-invariant probability measure `μ` and
every horospherical subgroup `U` there is a system `ν` of leafwise measures on a conull set
(Pisa Thm 6.3, EKL §2.1). -/
def P_LeafwiseEx : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
    ∀ U : Subgroup SL3, IsHoro U →
      ∃ (ν : X3 → Measure SL3) (Y : Set X3), IsLeafwise μ U ν Y

/-- Clauses (U3), (U4), (U5), (U7), (U8) of `P_Leafwise`, restricted to the one-dimensional
root groups `U_ij` (this is the part of the leafwise-measure input that the commutator lemma
C7 uses):

* (U3) `CrossSection μ (U_ij)` iff the leafwise measures are a.e. the Dirac mass at `1`;
* (U4) a.e. right-translation invariance of the leafwise measures implies `U_ij`-invariance of
  `μ` (this is the direction of EKL (6) / Pisa 6.27 that the commutator argument consumes, and
  the one that is available in the workspace as `Work.EKLRelCross.isUInvariant_of_aeHaar`);
* (U5) a leafwise measure proportional to one of its right translates is equal to it;
* (U7) `A`-covariance of the leafwise measures on a single conull set;
* (U8) the ergodic dichotomy: conull cross-section, or no atom at the identity. -/
def P_RootProps : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAErgodic μ → ∀ {i j : Fin 3} (hij : i ≠ j)
    (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ (Uij hij) ν X' →
    (CrossSection μ (Uij hij) ↔ ∀ᵐ x ∂μ, ν x = Measure.dirac 1) ∧
    ((∀ᵐ x ∂μ, ∀ u ∈ Uij hij, (ν x).map (fun g => g * u) = ν x) →
        IsUInvariant μ (Uij hij)) ∧
    (∀ᵐ x ∂μ, ∀ u ∈ Uij hij, ∀ c : ℝ≥0∞, (ν x).map (fun g => g * u) = c • ν x →
        (ν x).map (fun g => g * u) = ν x) ∧
    (∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
        ∀ (t : Fin 3 → ℝ) (x : X3), x ∈ X'' → aDiag t • x ∈ X'' →
          ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (aDiag t • x) = c • (ν x).map (fun g => aDiag t * g * (aDiag t)⁻¹)) ∧
    (CrossSection μ (Uij hij) ∨ ∀ᵐ x ∂μ, ν x {1} = 0)

end Work.EKLC7
