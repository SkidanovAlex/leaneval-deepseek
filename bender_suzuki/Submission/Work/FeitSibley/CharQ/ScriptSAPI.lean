import Mathlib
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr
import Submission.Work.FeitSibley.CharQ.prodChar_conjFun
import Submission.Work.Clifford.clifford_correspondence
import Submission.Work.Clifford.clifford_constituents
import Submission.Work.CharCore.Main
import Submission.Work.Frobenius.Induced.irr_eq_one_of_fpf
import Submission.Work.Frobenius.Bridge.mem_Irr_iff_coherence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.CharQ.ScriptSAPI`

Vocabulary and elementary facts for the equality
`scriptS h.H h.Q₁ = {Ind_Q^H φ | φ ∈ Irr Q, Q₁ ⊄ ker φ}` (`scriptS_eq_image`).

The whole computation happens in the group `H = ↥h.H`, with `Q` replaced by
`N := h.Q.subgroupOf h.H ⊴ H`; `eQ h : ↥N ≃* ↥h.Q` is the canonical identification and
`pull h φ = φ ∘ eQ h` transports a function on `↥h.Q` to a function on `↥N`.  By construction
`h.indQH φ = Work.Clifford.indFun N (pull h φ)`.

Main contents:

* `eQ`, `toQ`, `pull` and their basic API (`pull_toQ`, `pull_one`, `pull_mem_Irr`, …);
* `fpf_Irr_Q1`: a non-trivial `d ∈ D` fixes no non-trivial irreducible character of `Q₁`
  (the fixed-point-freeness of `D` on `Q₁`, in the form needed below);
* the bridges `indQH_eq_indFun`, `induction_conjFun_eq_clifford`, `conjFun_pull_of_mem_D`,
  `conjFun_pull_of_mem_Q`, `conjFun_Q1_eq_comp_conjMap`;
* `prodChar_Q1_component_ne_trivial`: if `prodChar h lam theta` is non-trivial on `Q₁` then
  `theta ≠ 1`.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.CharQ

variable {G : Type} [Group G] [Fintype G]

/-- `Q`, viewed as a subgroup of `H`, is normal in `H`. -/
instance instNormalQsubgroupOf (h : Work.FeitSibley.FSData G) :
    (h.Q.subgroupOf h.H).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer h.Q_normal_in_H

/-- The canonical isomorphism `↥(h.Q.subgroupOf h.H) ≃* ↥h.Q`. -/
noncomputable def eQ (h : Work.FeitSibley.FSData G) : ↥(h.Q.subgroupOf h.H) ≃* ↥h.Q :=
  Subgroup.subgroupOfEquivOfLe h.Q_le_H

@[simp] theorem eQ_apply_val (h : Work.FeitSibley.FSData G) (x : ↥(h.Q.subgroupOf h.H)) :
    ((eQ h x : ↥h.Q) : G) = ((x : ↥h.H) : G) := rfl

/-- The element of `↥(h.Q.subgroupOf h.H)` corresponding to an element of `↥h.Q`. -/
noncomputable def toQ (h : Work.FeitSibley.FSData G) (x : ↥h.Q) : ↥(h.Q.subgroupOf h.H) :=
  (eQ h).symm x

@[simp] theorem toQ_coe (h : Work.FeitSibley.FSData G) (x : ↥h.Q) :
    ((toQ h x : ↥(h.Q.subgroupOf h.H)) : ↥h.H) = ⟨(x : G), h.Q_le_H x.2⟩ :=
  Subtype.ext rfl

@[simp] theorem eQ_toQ (h : Work.FeitSibley.FSData G) (x : ↥h.Q) : eQ h (toQ h x) = x :=
  (eQ h).apply_symm_apply x

/-- The pullback of a function on `↥h.Q` to `↥(h.Q.subgroupOf h.H)`. -/
noncomputable def pull (h : Work.FeitSibley.FSData G) (φ : ↥h.Q → ℂ) :
    ↥(h.Q.subgroupOf h.H) → ℂ :=
  fun x => φ ⟨(x : G), x.2⟩

@[simp] theorem pull_apply (h : Work.FeitSibley.FSData G) (φ : ↥h.Q → ℂ)
    (x : ↥(h.Q.subgroupOf h.H)) : pull h φ x = φ ⟨(x : G), x.2⟩ := rfl

/-- `pull` is precomposition with `eQ`. -/
theorem pull_apply_eQ (h : Work.FeitSibley.FSData G) (φ : ↥h.Q → ℂ)
    (x : ↥(h.Q.subgroupOf h.H)) : pull h φ x = φ (eQ h x) :=
  congrArg φ (Subtype.ext rfl)

theorem pull_eq_comp_eQ (h : Work.FeitSibley.FSData G) (φ : ↥h.Q → ℂ) :
    pull h φ = fun x => φ (eQ h x) :=
  funext fun x => pull_apply_eQ h φ x

@[simp] theorem pull_toQ (h : Work.FeitSibley.FSData G) (φ : ↥h.Q → ℂ) (x : ↥h.Q) :
    pull h φ (toQ h x) = φ x := by
  rw [pull_apply_eQ, eQ_toQ]

@[simp] theorem pull_one (h : Work.FeitSibley.FSData G) (φ : ↥h.Q → ℂ) :
    pull h φ 1 = φ 1 := by
  rw [pull_apply_eQ, map_one]

/-- `h.indQH φ` is the induction of the pullback of `φ` to `h.Q.subgroupOf h.H`. -/
theorem indQH_eq_indFun (h : Work.FeitSibley.FSData G) (φ : ↥h.Q → ℂ) :
    h.indQH φ = Work.Clifford.indFun (h.Q.subgroupOf h.H) (pull h φ) := rfl

/-- The pullback of an irreducible character of `Q` is an irreducible character of
`Q` viewed inside `H`. -/
theorem pull_mem_Irr (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    (hφ : φ ∈ Work.CharCore.Irr ↥h.Q) : pull h φ ∈ Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) := by
  have h1 : (fun x : ↥(h.Q.subgroupOf h.H) => φ (eQ h x)) ∈
      Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
    Work.Clifford.Irr_comp_mulEquiv (eQ h) ((Work.Clifford.corr_mem_Irr_charCore).mpr hφ)
  rwa [pull_eq_comp_eQ h φ]

/-- Every element of the core's `Irr` is an irreducible character in the Frobenius interface. -/
theorem mem_Frobenius_Irr_of_mem_Irr {K : Type} [Group K] [Fintype K] {θ : K → ℂ}
    (h : θ ∈ Work.CharCore.Irr K) : θ ∈ Work.Frobenius.Irr K :=
  (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr ((Work.CharCore.mem_Irr_iff_fdrep θ).mp h)

/-! ### Fixed-point-freeness of `D` on `Q₁` -/

/-- Conjugation by `d` (in the normalizer of `Q₁`) as an endomorphism of `Q₁`. -/
noncomputable def conjMapQ1 (h : Work.FeitSibley.FSData G) (d : G)
    (hdn : d ∈ Subgroup.normalizer (h.Q1 : Set G)) : ↥h.Q1 →* ↥h.Q1 where
  toFun x := ⟨d * (x : G) * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdn (x : G)).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] theorem conjMapQ1_val (h : Work.FeitSibley.FSData G) (d : G)
    (hdn : d ∈ Subgroup.normalizer (h.Q1 : Set G)) (x : ↥h.Q1) :
    ((conjMapQ1 h d hdn x : ↥h.Q1) : G) = d * (x : G) * d⁻¹ := rfl

/-- `Work.Induction.conjFun` on `Q₁` is precomposition with `conjMapQ1`. -/
theorem conjFun_Q1_eq_comp_conjMap (h : Work.FeitSibley.FSData G) {d : G}
    (hdn : d ∈ Subgroup.normalizer (h.Q1 : Set G)) (theta : ↥h.Q1 → ℂ) :
    Work.Induction.conjFun h.Q1 ⟨d, hdn⟩ theta = fun x => theta (conjMapQ1 h d hdn x) := by
  funext x
  rw [Work.Induction.conjFun_apply]
  rfl

/-- A nontrivial `d ∈ D` has no nontrivial fixed point on `Q₁`. -/
theorem conjMapQ1_fixed_imp_eq_one (h : Work.FeitSibley.FSData G) {d : G} (hd : d ∈ h.D)
    (hd1 : d ≠ 1) (hdn : d ∈ Subgroup.normalizer (h.Q1 : Set G)) :
    ∀ x : ↥h.Q1, conjMapQ1 h d hdn x = x → x = 1 := by
  intro x hx
  have hv : d * (x : G) * d⁻¹ = (x : G) := congrArg Subtype.val hx
  exact Subtype.ext (h.D_fpf_Q1 d hd hd1 (x : G) x.2 hv)

/-- **A nontrivial element of `D` fixes no nontrivial irreducible character of `Q₁`.** -/
theorem fpf_Irr_Q1 (h : Work.FeitSibley.FSData G) {d : G} (hd : d ∈ h.D) (hd1 : d ≠ 1)
    {theta : ↥h.Q1 → ℂ} (htheta : theta ∈ Work.CharCore.Irr ↥h.Q1)
    (hinv : ∀ x : ↥h.Q1, theta (conjMapQ1 h d (h.Q1_normal_in_H (h.D_le_H hd)) x) = theta x) :
    theta = fun _ : ↥h.Q1 => 1 :=
  Work.Frobenius.Induced.irr_eq_one_of_fpf (conjMapQ1 h d (h.Q1_normal_in_H (h.D_le_H hd)))
    (conjMapQ1_fixed_imp_eq_one h hd hd1 (h.Q1_normal_in_H (h.D_le_H hd)))
    (mem_Frobenius_Irr_of_mem_Irr htheta) hinv

/-! ### Conjugation bridges -/

/-- `Work.Induction.conjFun` and `Work.Clifford.conjFun` are the same function. -/
theorem induction_conjFun_eq_clifford {N : Subgroup G} [N.Normal] {d : G}
    (hdn : d ∈ Subgroup.normalizer (N : Set G)) (f : ↥N → ℂ) :
    Work.Induction.conjFun N ⟨d, hdn⟩ f = Work.Clifford.conjFun N d f := by
  funext n
  rw [Work.Induction.conjFun_apply, Work.Clifford.conjFun_apply]
  exact congrArg f (Subtype.ext rfl)

/-- Conjugation by `d ∈ D` on a pullback is the pullback of the conjugation by `d` on `Q`. -/
theorem conjFun_pull_of_mem_D (h : Work.FeitSibley.FSData G) {d : G} (hd : d ∈ h.D)
    (φ : ↥h.Q → ℂ) :
    Work.Clifford.conjFun (h.Q.subgroupOf h.H) (⟨d, h.D_le_H hd⟩ : ↥h.H) (pull h φ) =
      pull h (Work.Induction.conjFun h.Q ⟨d, h.Q_normal_in_H (h.D_le_H hd)⟩ φ) := by
  funext x
  rw [Work.Clifford.conjFun_apply]
  simp only [pull]
  rw [Work.Induction.conjFun_apply]
  apply congrArg φ
  apply Subtype.ext
  simp only [Work.Induction.conjMem_val, Subgroup.coe_mul, Subgroup.coe_inv]

/-- Conjugation by an element of `Q` (as an element of `H`) fixes the pullback of every class
function on `Q`. -/
theorem conjFun_pull_of_mem_Q (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    (hclass : Work.CharCore.IsClassFun φ) (q : ↥(h.Q.subgroupOf h.H)) :
    Work.Clifford.conjFun (h.Q.subgroupOf h.H) (q : ↥h.H) (pull h φ) = pull h φ := by
  haveI hN : (h.Q.subgroupOf h.H).Normal := instNormalQsubgroupOf h
  funext x
  rw [Work.Clifford.conjFun_apply]
  rw [pull_apply_eQ]
  have harg : (⟨(q : ↥h.H) * x * (q : ↥h.H)⁻¹, hN.conj_mem x x.2 (q : ↥h.H)⟩ :
      ↥(h.Q.subgroupOf h.H)) = q * x * q⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv])
  rw [harg, map_mul, map_mul, map_inv, pull_apply_eQ]
  exact hclass (eQ h x) (eQ h q)

/-! ### Two elementary facts on character values -/

/-- A complex number whose real part is `c ≥ 0` and whose norm is at most `c` equals `c`. -/
theorem complex_eq_of_re_eq_norm_le {z : ℂ} {c : ℝ} (h1 : z.re = c) (h2 : ‖z‖ ≤ c) : z = c := by
  have hc : 0 ≤ c := le_trans (norm_nonneg z) h2
  have him : z.im = 0 := by
    have hs : z.im ^ 2 = 0 := by
      have h1' : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      have h2' : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.normSq_apply]; ring
      have h3 : z.im ^ 2 = ‖z‖ ^ 2 - c ^ 2 := by
        rw [← h1', h2', h1]; ring
      have h4 : ‖z‖ ^ 2 ≤ c ^ 2 := by nlinarith [norm_nonneg z, h2]
      have h5 : z.im ^ 2 ≤ 0 := by rw [h3]; linarith
      exact le_antisymm h5 (sq_nonneg z.im)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
  have hre : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hre, h1]

/-- If the real part of the value of an irreducible character at `x` is the degree, then the
character is trivial at `x`. -/
theorem character_apply_eq_deg_of_re {K : Type} [Group K] [Fintype K] {ψ : K → ℂ}
    (hψ : ψ ∈ Work.CharCore.Irr K) (x : K)
    (h : (ψ x).re = (Work.CharCore.irrDeg ψ : ℝ)) : ψ x = ψ 1 := by
  have h2 : ‖ψ x‖ ≤ ((Work.CharCore.irrDeg ψ : ℕ) : ℝ) := Work.CharCore.norm_char_le hψ x
  have h3 : ψ x = ((Work.CharCore.irrDeg ψ : ℕ) : ℂ) := by
    simpa using complex_eq_of_re_eq_norm_le h h2
  rw [h3, ← Work.CharCore.irrDeg_spec hψ]

/-! ### The `Q₁`-component of a product character -/

/-- If `prodChar h lam theta` is non-trivial on `Q₁` then `theta` is not the trivial
character of `Q₁`. -/
theorem prodChar_Q1_component_ne_trivial (h : Work.FeitSibley.FSData G) {lam : ↥h.S → ℂ}
    {theta : ↥h.Q1 → ℂ} (hlam : lam ∈ Work.CharCore.Irr ↥h.S)
    (hw : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ h.prodChar lam theta x ≠ h.prodChar lam theta 1) :
    theta ≠ fun _ : ↥h.Q1 => 1 := by
  have hlam1 : lam 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hlam]
    exact_mod_cast (Work.CharCore.irrDeg_pos hlam).ne'
  obtain ⟨x, hxQ1, hxne⟩ := hw
  obtain ⟨a, ha, b, hb, hab⟩ := h.mem_Q_decomp x.2
  have hdec := h.mul_eq_of_Q_decomp ha (Subgroup.one_mem h.S) hb hxQ1 (by rw [← hab, one_mul])
  have ha1 : a = 1 := hdec.1
  have hval : h.prodChar lam theta x = lam 1 * theta ⟨b, hb⟩ := by
    have h1 : h.prodIso (⟨a, ha⟩, ⟨b, hb⟩) = x := by
      apply Subtype.ext
      simp only [Work.FeitSibley.FSData.prodIso_apply, Work.FeitSibley.FSData.prodHom_apply]
      exact hab.symm
    rw [← h1, h.prodChar_apply, show (⟨a, ha⟩ : ↥h.S) = 1 from Subtype.ext ha1]
  intro htriv
  have hb1 : theta ⟨b, hb⟩ = theta 1 := by rw [htriv]
  exact hxne (by rw [hval, h.prodChar_one lam theta, hb1])

end Work.FeitSibley.CharQ
