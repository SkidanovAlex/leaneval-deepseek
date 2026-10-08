import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.Clifford.card_charOrbit
import Submission.Work.Clifford.clifford_decomposition
import Submission.Work.Clifford.cfInner_indFun
import Submission.Work.Clifford.cfInner_orbitSum_eq_ite
import Submission.Work.Clifford.clifford_induction_mem_Irr
import Submission.Work.Induction.indFun_conjFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.card_fibre_indQH`

Let `h : FSData G` be the Feit–Sibley configuration (`H = Q ⋊ D`, `Q = S × Q₁`, `D` acting
fixed-point-freely on `Q₁`), and let `φ ∈ Irr Q` be non-trivial on `Q₁`.  Then the fibre of the
map `φ' ↦ Ind_Q^H φ'` over `Ind_Q^H φ` consists *exactly* of the `|D|` conjugates of `φ` by the
elements of `D`; in particular it has `|D|` elements.

## The mathematics

By `inertia_pull_eq`, the inertia group of `φ` (non-trivial on `Q₁`) is `Q`, so `χ := Ind_Q^H φ`
is irreducible (`indQH_mem_Irr_of_inertia`) and `χ|_Q = ∑_{ψ ∈ orbit of φ} ψ` is a sum over a
single orbit of length `|D|` (Clifford's theorem).

* Every conjugate `φ^d` (`d ∈ D`) satisfies `φ^d ∈ Irr Q` (conjugation by an automorphism
  preserves irreducibility) and `Ind φ^d = Ind φ` (induction is invariant under conjugation by
  an element of the normalizer, `Work.Induction.indFun_conjFun`).
* Conversely, if `Ind φ' = χ` then by Frobenius reciprocity `φ'` is a constituent of
  `χ|_Q = e · orbitSum θ₀`, hence (orthonormality of `Irr Q`) lies in the orbit of `θ₀`; the
  same is true of `φ`, so `φ'` is conjugate to `φ` by some `g ∈ H`; writing `g = q d` with
  `q ∈ Q`, `d ∈ D` and observing that `q` acts trivially on class functions of `Q`,
  `φ' = φ^d`.
* The map `d ↦ φ^d` is injective on `D`: if `φ^d = φ^{d'}` then `d d'⁻¹` lies in the inertia
  group of `φ`, which is `Q`, while `d d'⁻¹ ∈ D` and `Q ∩ D = 1`.

## Layout

* `dH`, `dNorm`, `conjQ` — the conjugate of a character of `Q` by an element of `D`;
* `pull_injective`, `pull_mem_Irr_iff` — transport of irreducibility along `pull`;
* `indFun_clifford_conjFun` — conjugation-invariance of induction, in the `Clifford` vocabulary;
* `conjQ_mem_Irr`, `indQH_conjQ` — the members of the fibre;
* `conjQ_inj`, `exists_conjQ_of_indQH_eq` — the map `d ↦ φ^d` is injective with image the fibre;
* `card_fibre_indQH` — the theorem.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.FeitSibley.CharQ

variable {G : Type} [Group G] [Fintype G]

/-! ### Some generalities -/

/-- `pull h` is injective: it is the pullback along the bijection `eQ h`. -/
theorem pull_injective (h : Work.FeitSibley.FSData G) : Function.Injective (pull h) := by
  intro φ ψ hφψ
  funext x
  simpa using congrFun hφψ (toQ h x)

/-- A function on `Q` is an irreducible character iff its pullback to `Q` viewed inside `H` is
(the two differ by the group isomorphism `eQ h`). -/
theorem pull_mem_Irr_iff (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ} :
    pull h φ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) ↔ φ ∈ Work.CharCore.Irr ↥h.Q := by
  constructor
  · intro h1
    have h2 : (fun y : ↥h.Q => pull h φ ((eQ h).symm y)) ∈ Work.Clifford.Irr ↥h.Q :=
      Work.Clifford.Irr_comp_mulEquiv (eQ h).symm h1
    have h3 : (fun y : ↥h.Q => pull h φ ((eQ h).symm y)) = φ := by
      funext y
      show φ ⟨(((eQ h).symm y : ↥(h.Q.subgroupOf h.H)) : G), _⟩ = φ y
      exact congrArg φ (Subtype.ext rfl)
    rw [h3] at h2
    exact (Work.Clifford.corr_mem_Irr_charCore).mp h2
  · intro hφ
    exact pull_mem_Irr h hφ

/-- Induction of a conjugate is independent of the conjugating element of the normalizer: the
`Clifford` version of `Work.Induction.indFun_conjFun`. -/
theorem indFun_clifford_conjFun {M : Type} [Group M] [Fintype M] {N : Subgroup M} [N.Normal]
    (x : Work.Induction.normalizer N) (f : ↥N → ℂ) :
    Work.Induction.indFun N (Work.Clifford.conjFun N (x : M) f) = Work.Induction.indFun N f := by
  rw [show Work.Clifford.conjFun N (x : M) f =
      Work.Induction.conjFun N x f from (induction_conjFun_eq_clifford x.2 f).symm]
  exact Work.Induction.indFun_conjFun N x f

end Work.FeitSibley.CharQ

namespace Work.FeitSibley

variable {G : Type} [Group G] [Fintype G]

namespace FSData

variable (h : FSData G)

/-- An element of `D`, viewed as an element of `H`. -/
abbrev dH (d : ↥h.D) : ↥h.H := ⟨(d : G), h.D_le_H d.2⟩

/-- An element of `D` as an element of the normalizer of `Q` in `G`. -/
abbrev dNorm (d : ↥h.D) : Work.Induction.normalizer h.Q :=
  ⟨(d : G), h.Q_normal_in_H (h.D_le_H d.2)⟩

/-- The conjugate `φ^d` of a function `φ` on `Q` by an element `d` of `D` (which normalizes
`Q`): `φ^d(x) = φ (d x d⁻¹)`. -/
noncomputable def conjQ (d : ↥h.D) (φ : ↥h.Q → ℂ) : ↥h.Q → ℂ :=
  Work.Induction.conjFun h.Q (h.dNorm d) φ

/-- Pulling back the conjugate by `d ∈ D` is conjugation of the pullback by `d` in `H`. -/
theorem pull_conjQ (d : ↥h.D) (φ : ↥h.Q → ℂ) :
    Work.FeitSibley.CharQ.pull h (h.conjQ d φ) =
      Work.Clifford.conjFun (h.Q.subgroupOf h.H) (h.dH d)
        (Work.FeitSibley.CharQ.pull h φ) :=
  (Work.FeitSibley.CharQ.conjFun_pull_of_mem_D h d.2 φ).symm

/-- Conjugates of irreducible characters of `Q` by elements of `D` are irreducible. -/
theorem conjQ_mem_Irr {φ : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q) (d : ↥h.D) :
    h.conjQ d φ ∈ Work.CharCore.Irr ↥h.Q := by
  have h1 : Work.Clifford.conjFun (h.Q.subgroupOf h.H) (h.dH d)
      (Work.FeitSibley.CharQ.pull h φ) ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
    Work.Clifford.conjFun_mem_Irr (h.dH d) (Work.FeitSibley.CharQ.pull_mem_Irr h hφ)
  rw [← h.pull_conjQ d φ] at h1
  exact (Work.FeitSibley.CharQ.pull_mem_Irr_iff h).mp h1

/-- Conjugation by `D` does not change the induced character `Ind_Q^H`. -/
theorem indQH_conjQ (d : ↥h.D) (φ : ↥h.Q → ℂ) :
    h.indQH (h.conjQ d φ) = h.indQH φ := by
  show Work.Induction.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h (h.conjQ d φ)) =
    Work.Induction.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ)
  rw [h.pull_conjQ d φ]
  exact Work.FeitSibley.CharQ.indFun_clifford_conjFun
    ⟨h.dH d, Subgroup.le_normalizer_of_normal (K := ⊤) (Subgroup.mem_top _)⟩
    (Work.FeitSibley.CharQ.pull h φ)

/-- The conjugates of `φ` by two elements of `D` coincide only if the elements do: the map
`d ↦ φ^d` is injective as soon as `φ` is non-trivial on `Q₁`. -/
theorem conjQ_inj {φ : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hw : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1) {d d' : ↥h.D}
    (hdd' : h.conjQ d φ = h.conjQ d' φ) : d = d' := by
  have hI := Work.FeitSibley.CharQ.inertia_pull_eq h hφ hw
  have hpull : Work.FeitSibley.CharQ.pull h (h.conjQ d φ) =
      Work.FeitSibley.CharQ.pull h (h.conjQ d' φ) := by rw [hdd']
  rw [h.pull_conjQ d φ, h.pull_conjQ d' φ] at hpull
  have hmem : (h.dH d) * (h.dH d')⁻¹ ∈ h.Q.subgroupOf h.H := by
    rw [← hI]
    exact (Work.Clifford.conjFun_eq_conjFun_iff (Work.FeitSibley.CharQ.pull h φ)
      (h.dH d) (h.dH d')).mp hpull
  have hmemQ : (((h.dH d) * (h.dH d')⁻¹ : ↥h.H) : G) ∈ h.Q := hmem
  have hmemD : (((h.dH d) * (h.dH d')⁻¹ : ↥h.H) : G) ∈ h.D :=
    mul_mem d.2 (inv_mem d'.2)
  have hone : (((h.dH d) * (h.dH d')⁻¹ : ↥h.H) : G) = 1 := by
    have h1 : (((h.dH d) * (h.dH d')⁻¹ : ↥h.H) : G) ∈ h.Q ⊓ h.D := ⟨hmemQ, hmemD⟩
    rw [h.Q_inf_D] at h1
    simpa using h1
  refine Subtype.ext (mul_inv_eq_one.mp ?_)
  have h2 : (((h.dH d) * (h.dH d')⁻¹ : ↥h.H) : G) = (d : G) * (d' : G)⁻¹ := rfl
  rw [← h2]
  exact hone

/-- **The fibre of `Ind_Q^H` is the `D`-orbit.**  If `φ ∈ Irr Q` is non-trivial on `Q₁` and
`φ' ∈ Irr Q` induces the same character of `H`, then `φ'` is the conjugate of `φ` by an element
of `D`. -/
theorem exists_conjQ_of_indQH_eq {φ φ' : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hw : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1)
    (hφ' : φ' ∈ Work.CharCore.Irr ↥h.Q) (heq : h.indQH φ' = h.indQH φ) :
    ∃ d : ↥h.D, φ' = h.conjQ d φ := by
  have hθ : Work.FeitSibley.CharQ.pull h φ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
    Work.FeitSibley.CharQ.pull_mem_Irr h hφ
  have hψ : Work.FeitSibley.CharQ.pull h φ' ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
    Work.FeitSibley.CharQ.pull_mem_Irr h hφ'
  have hχIrr : h.indQH φ ∈ Work.Clifford.Irr ↥h.H :=
    (Work.Clifford.corr_mem_Irr_charCore).mpr
      (Work.FeitSibley.CharQ.indQH_mem_Irr_of_inertia h hφ
        (Work.FeitSibley.CharQ.inertia_pull_eq h hφ hw))
  have hχclass : Work.Clifford.IsClassFun (h.indQH φ) :=
    Work.Clifford.IsClassFun.of_mem_Irr hχIrr
  obtain ⟨θ₀, hθ₀, e, hepos, hdec⟩ :=
    Work.Clifford.clifford_decomposition (N := h.Q.subgroupOf h.H) hχIrr
  -- the two induced functions agree
  have hindeq : Work.Clifford.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ') =
      Work.Clifford.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) := by
    rw [← Work.FeitSibley.CharQ.indQH_eq_indFun h φ', heq,
      Work.FeitSibley.CharQ.indQH_eq_indFun h φ]
  -- every constituent of `χ|_Q` lies in the orbit of `θ₀`
  have hmem_orbit : ∀ {θ' : ↥(h.Q.subgroupOf h.H) → ℂ},
      θ' ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) →
      Work.Clifford.cfInner θ'
        (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ)) ≠ 0 →
      θ' ∈ Work.Clifford.charOrbit (h.Q.subgroupOf h.H) θ₀ := by
    intro θ' hθ' hne
    have h2 : Work.Clifford.cfInner (Work.Clifford.orbitSum (h.Q.subgroupOf h.H) θ₀) θ' ≠ 0 := by
      intro hz
      apply hne
      rw [hdec, Work.Clifford.cfInner_smul_right,
        show Work.Clifford.cfInner θ' (Work.Clifford.orbitSum (h.Q.subgroupOf h.H) θ₀) =
            starRingEnd ℂ (Work.Clifford.cfInner (Work.Clifford.orbitSum
              (h.Q.subgroupOf h.H) θ₀) θ') from Work.Clifford.cfInner_conj_symm _ _,
        hz, map_zero, mul_zero]
    rw [Work.Clifford.cfInner_orbitSum_eq_ite hθ₀ hθ'] at h2
    by_contra hnot
    rw [if_neg hnot] at h2
    exact h2 rfl
  -- both `pull φ'` and `pull φ` are constituents
  have hone_ψ : Work.Clifford.cfInner (Work.FeitSibley.CharQ.pull h φ')
      (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ)) = 1 := by
    rw [← Work.Clifford.cfInner_indFun (H := h.Q.subgroupOf h.H)
      (Work.FeitSibley.CharQ.pull h φ') hχclass, hindeq]
    show Work.Clifford.cfInner (h.indQH φ) (h.indQH φ) = 1
    rw [Work.Clifford.cfInner_eq_ite_of_mem_Irr hχIrr hχIrr, if_pos rfl]
  have hone_θ : Work.Clifford.cfInner (Work.FeitSibley.CharQ.pull h φ)
      (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ)) = 1 := by
    rw [← Work.Clifford.cfInner_indFun (H := h.Q.subgroupOf h.H)
      (Work.FeitSibley.CharQ.pull h φ) hχclass]
    show Work.Clifford.cfInner (h.indQH φ) (h.indQH φ) = 1
    rw [Work.Clifford.cfInner_eq_ite_of_mem_Irr hχIrr hχIrr, if_pos rfl]
  have hψo : Work.FeitSibley.CharQ.pull h φ' ∈
      Work.Clifford.charOrbit (h.Q.subgroupOf h.H) θ₀ :=
    hmem_orbit hψ (by rw [hone_ψ]; exact one_ne_zero)
  have hθo : Work.FeitSibley.CharQ.pull h φ ∈
      Work.Clifford.charOrbit (h.Q.subgroupOf h.H) θ₀ :=
    hmem_orbit hθ (by rw [hone_θ]; exact one_ne_zero)
  -- `pull φ'` is conjugate to `pull φ` in `H`
  have hmemψ : Work.FeitSibley.CharQ.pull h φ' ∈
      Work.Clifford.charOrbit (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) := by
    rw [Work.Clifford.charOrbit_eq_of_mem hθo]
    exact hψo
  obtain ⟨g, hg⟩ := Work.Clifford.mem_charOrbit.mp hmemψ
  -- reduce the conjugating element to an element of `D`
  obtain ⟨q₀, hq₀, d₀, hd₀, hgd⟩ := h.mem_H_decomp g.2
  have hgdecomp : g = (⟨q₀, h.Q_le_H hq₀⟩ : ↥h.H) * (⟨d₀, h.D_le_H hd₀⟩ : ↥h.H) :=
    Subtype.ext hgd
  have hqfix : Work.Clifford.conjFun (h.Q.subgroupOf h.H) (⟨q₀, h.Q_le_H hq₀⟩ : ↥h.H)
      (Work.FeitSibley.CharQ.pull h φ) = Work.FeitSibley.CharQ.pull h φ :=
    Work.Clifford.conjFun_eq_self_of_isClassFun (Work.Clifford.IsClassFun.of_mem_Irr hθ)
      (Subgroup.mem_subgroupOf.mpr hq₀)
  have hψeq : Work.Clifford.conjFun (h.Q.subgroupOf h.H) (⟨d₀, h.D_le_H hd₀⟩ : ↥h.H)
      (Work.FeitSibley.CharQ.pull h φ) = Work.FeitSibley.CharQ.pull h φ' := by
    have h1 : Work.Clifford.conjFun (h.Q.subgroupOf h.H) (⟨d₀, h.D_le_H hd₀⟩ : ↥h.H)
        (Work.FeitSibley.CharQ.pull h φ) =
        Work.Clifford.conjFun (h.Q.subgroupOf h.H) g (Work.FeitSibley.CharQ.pull h φ) := by
      rw [hgdecomp, Work.Clifford.conjFun_mul, hqfix]
    rw [h1, hg]
  refine ⟨⟨d₀, hd₀⟩, ?_⟩
  have hlast : Work.FeitSibley.CharQ.pull h φ' =
      Work.FeitSibley.CharQ.pull h (h.conjQ ⟨d₀, hd₀⟩ φ) := by
    rw [h.pull_conjQ ⟨d₀, hd₀⟩ φ]
    exact hψeq.symm
  exact Work.FeitSibley.CharQ.pull_injective h hlast

/-- **The fibre of `Ind_Q^H` over `Ind_Q^H φ` has `|D|` elements** (for `φ ∈ Irr Q` non-trivial
on `Q₁`). -/
theorem card_fibre_indQH_aux {φ : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hw : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1) :
    Nat.card {φ' : ↥h.Q → ℂ // φ' ∈ Work.CharCore.Irr ↥h.Q ∧ h.indQH φ' = h.indQH φ}
      = Nat.card h.D := by
  have hset : {φ' : ↥h.Q → ℂ | φ' ∈ Work.CharCore.Irr ↥h.Q ∧ h.indQH φ' = h.indQH φ} =
      Set.range (fun d : ↥h.D => h.conjQ d φ) := by
    ext φ'
    constructor
    · rintro ⟨hφ', heq⟩
      obtain ⟨d, hd⟩ := h.exists_conjQ_of_indQH_eq hφ hw hφ' heq
      exact ⟨d, hd.symm⟩
    · rintro ⟨d, rfl⟩
      exact ⟨h.conjQ_mem_Irr hφ d, h.indQH_conjQ d φ⟩
  have hinj : Function.Injective (fun d : ↥h.D => h.conjQ d φ) := by
    intro d d' hdd'
    exact h.conjQ_inj hφ hw hdd'
  calc Nat.card {φ' : ↥h.Q → ℂ // φ' ∈ Work.CharCore.Irr ↥h.Q ∧ h.indQH φ' = h.indQH φ}
      = Nat.card ↥(Set.range (fun d : ↥h.D => h.conjQ d φ)) :=
        Nat.card_congr (Set.equivOfEq hset)
    _ = Nat.card ↥h.D :=
        Nat.card_congr (Equiv.ofInjective (fun d : ↥h.D => h.conjQ d φ) hinj).symm
    _ = Nat.card h.D := rfl

end FSData

end Work.FeitSibley

namespace Work.FeitSibley.CharQ

theorem card_fibre_indQH {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {φ : ↥h.Q → ℂ} (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hw : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1) :
    Nat.card {φ' : ↥h.Q → ℂ // φ' ∈ Work.CharCore.Irr ↥h.Q ∧ h.indQH φ' = h.indQH φ}
      = Nat.card h.D :=
  h.card_fibre_indQH_aux hφ hw

end Work.FeitSibley.CharQ
