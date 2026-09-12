import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.closure_P_eq_S_of_degree_le_one
import Submission.Commons.LorentzianPolynomials.closure_P_eq_nonneg
import Submission.Commons.Combinatorics.MvPolynomial.support_MConvex_of_homogeneous_Rayleigh
import Submission.Commons.LorentzianPolynomials.L_subset_Rayleigh

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

noncomputable section

local instance instAddCommGroupHCSL6 (n d : ℕ) : AddCommGroup (H n d) := by
  dsimp [H]
  exact (homogeneousSubmodule (Fin n) ℝ d).addCommGroup

local instance instModuleHCSL6 (n d : ℕ) : Module ℝ (H n d) := by
  dsimp [H]
  exact (homogeneousSubmodule (Fin n) ℝ d).module

local instance instIsModuleTopologyHCSL6 (n d : ℕ) : IsModuleTopology ℝ (H n d) where
  eq_moduleTopology' := by
    dsimp [H, instTopologicalSpaceH]

private lemma csl_Ŀ_subset_P (n d : ℕ) : Ŀ n d ⊆ P n d := by
  intro f hf
  cases d with
  | zero => simpa [Ŀ] using hf
  | succ d =>
      cases d with
      | zero => simpa [Ŀ] using hf
      | succ d =>
          cases d with
          | zero => simpa [Ŀ] using hf.1
          | succ k => simpa [Ŀ] using hf.1

private noncomputable def csl_pderivL {n : ℕ} (l : List (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  l.foldl (fun q i => MvPolynomial.pderiv i q) p

private abbrev csl_RayCondPoly {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ), (∀ k : Fin n, 0 ≤ w k) →
    MvPolynomial.eval w (csl_pderivL l p) *
        MvPolynomial.eval w (csl_pderivL (i :: j :: l) p) ≤
      c * (MvPolynomial.eval w (csl_pderivL (i :: l) p) *
        MvPolynomial.eval w (csl_pderivL (j :: l) p))

private lemma csl_pderivL_add {n : ℕ} (l : List (Fin n)) (p q : MvPolynomial (Fin n) ℝ) :
    csl_pderivL l (p + q) = csl_pderivL l p + csl_pderivL l q := by
  revert p q
  induction l with
  | nil => intro p q; simp [csl_pderivL]
  | cons i l ih =>
      intro p q
      simp only [csl_pderivL, List.foldl_cons]
      rw [map_add]
      exact ih (pderiv i p) (pderiv i q)

private lemma csl_pderivL_smul {n : ℕ} (l : List (Fin n)) (a : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    csl_pderivL l (a • p) = a • csl_pderivL l p := by
  revert a p
  induction l with
  | nil => intro a p; simp [csl_pderivL]
  | cons i l ih =>
      intro a p
      simp only [csl_pderivL, List.foldl_cons]
      have hs : MvPolynomial.pderiv i (a • p) = a • MvPolynomial.pderiv i p := by
        exact (MvPolynomial.pderiv (R := ℝ) i : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ).map_smul a p
      rw [hs]
      exact ih a (MvPolynomial.pderiv i p)

private noncomputable def csl_evalDerivLM (n d : ℕ) (w : Fin n → ℝ) (l : List (Fin n)) : H n d →ₗ[ℝ] ℝ where
  toFun f := MvPolynomial.eval w (csl_pderivL l f.1)
  map_add' f g := by
    have hval : csl_pderivL l (f + g).1 = csl_pderivL l f.1 + csl_pderivL l g.1 := by
      rw [show (f + g).1 = f.1 + g.1 by rfl, csl_pderivL_add]
    rw [hval]
    simp
  map_smul' a f := by
    have hval : csl_pderivL l (a • f).1 = a • csl_pderivL l f.1 := by
      rw [show (a • f).1 = a • f.1 by rfl, csl_pderivL_smul]
    rw [hval]
    simp

private lemma csl_continuous_evalDeriv (n d : ℕ) (w : Fin n → ℝ) (l : List (Fin n)) :
    Continuous (fun f : H n d => MvPolynomial.eval w (csl_pderivL l f.1)) := by
  exact IsModuleTopology.continuous_of_linearMap (R := ℝ) (A := H n d) (B := ℝ) (csl_evalDerivLM n d w l)

private def csl_RayCondSet (n d : ℕ) (c : ℝ) : Set (H n d) :=
  {f : H n d | csl_RayCondPoly c f.1}

private lemma csl_isClosed_RayCondSet (n d : ℕ) (c : ℝ) : IsClosed (csl_RayCondSet n d c) := by
  classical
  unfold csl_RayCondSet
  have hSeteq : {f : H n d | csl_RayCondPoly c f.1} =
      ⋂ (l : List (Fin n)), ⋂ (i : Fin n), ⋂ (j : Fin n), ⋂ (w : Fin n → ℝ),
        {f : H n d | (∀ k : Fin n, 0 ≤ w k) →
          MvPolynomial.eval w (csl_pderivL l f.1) *
              MvPolynomial.eval w (csl_pderivL (i :: j :: l) f.1) ≤
            c * (MvPolynomial.eval w (csl_pderivL (i :: l) f.1) *
              MvPolynomial.eval w (csl_pderivL (j :: l) f.1))} := by
    ext f
    simp [csl_RayCondPoly]
  rw [hSeteq]
  refine isClosed_iInter (fun l => ?_)
  refine isClosed_iInter (fun i => ?_)
  refine isClosed_iInter (fun j => ?_)
  refine isClosed_iInter (fun w => ?_)
  by_cases hgood : ∀ k : Fin n, 0 ≤ w k
  · have hA : Continuous (fun x : H n d => MvPolynomial.eval w (csl_pderivL l x.1)) :=
      csl_continuous_evalDeriv n d w l
    have hB : Continuous (fun x : H n d => MvPolynomial.eval w (csl_pderivL (i :: j :: l) x.1)) :=
      csl_continuous_evalDeriv n d w (i :: j :: l)
    have hC : Continuous (fun x : H n d => MvPolynomial.eval w (csl_pderivL (i :: l) x.1)) :=
      csl_continuous_evalDeriv n d w (i :: l)
    have hD : Continuous (fun x : H n d => MvPolynomial.eval w (csl_pderivL (j :: l) x.1)) :=
      csl_continuous_evalDeriv n d w (j :: l)
    have hle : IsClosed {x : H n d |
        MvPolynomial.eval w (csl_pderivL l x.1) *
            MvPolynomial.eval w (csl_pderivL (i :: j :: l) x.1) ≤
          c * (MvPolynomial.eval w (csl_pderivL (i :: l) x.1) *
            MvPolynomial.eval w (csl_pderivL (j :: l) x.1))} := by
      exact isClosed_le (hA.mul hB) (continuous_const.mul (hC.mul hD))
    have hEq : {x : H n d | (∀ k : Fin n, 0 ≤ w k) →
          MvPolynomial.eval w (csl_pderivL l x.1) *
              MvPolynomial.eval w (csl_pderivL (i :: j :: l) x.1) ≤
            c * (MvPolynomial.eval w (csl_pderivL (i :: l) x.1) *
              MvPolynomial.eval w (csl_pderivL (j :: l) x.1))} =
        {x : H n d | MvPolynomial.eval w (csl_pderivL l x.1) *
              MvPolynomial.eval w (csl_pderivL (i :: j :: l) x.1) ≤
            c * (MvPolynomial.eval w (csl_pderivL (i :: l) x.1) *
              MvPolynomial.eval w (csl_pderivL (j :: l) x.1))} := by
      ext x
      simp [hgood]
    rwa [hEq]
  · have hEq : {x : H n d | (∀ k : Fin n, 0 ≤ w k) →
          MvPolynomial.eval w (csl_pderivL l x.1) *
              MvPolynomial.eval w (csl_pderivL (i :: j :: l) x.1) ≤
            c * (MvPolynomial.eval w (csl_pderivL (i :: l) x.1) *
              MvPolynomial.eval w (csl_pderivL (j :: l) x.1))} = univ := by
      ext x
      simp [hgood]
    rw [hEq]
    exact isClosed_univ

private def csl_pderivLM (n k : ℕ) (i : Fin n) :
    H n (Nat.succ (Nat.succ (Nat.succ k))) →ₗ[ℝ] H n (Nat.succ (Nat.succ k)) where
  toFun f := ⟨f.1.pderiv i, f.2.pderiv⟩
  map_add' f g := by
    apply Subtype.ext
    change MvPolynomial.pderiv (R := ℝ) i (f.1 + g.1) =
      MvPolynomial.pderiv (R := ℝ) i f.1 + MvPolynomial.pderiv (R := ℝ) i g.1
    exact (MvPolynomial.pderiv (R := ℝ) i).map_add f.1 g.1
  map_smul' a f := by
    apply Subtype.ext
    change MvPolynomial.pderiv (R := ℝ) i (a • f.1) = a • MvPolynomial.pderiv (R := ℝ) i f.1
    exact (MvPolynomial.pderiv (R := ℝ) i : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ).map_smul a f.1

private def csl_pderivCLM (n k : ℕ) (i : Fin n) :
    H n (Nat.succ (Nat.succ (Nat.succ k))) →L[ℝ] H n (Nat.succ (Nat.succ k)) where
  toLinearMap := csl_pderivLM n k i
  cont := by
    haveI : ContinuousAdd (H n (Nat.succ (Nat.succ k))) :=
      IsModuleTopology.toContinuousAdd (R := ℝ) (A := H n (Nat.succ (Nat.succ k)))
    haveI : ContinuousSMul ℝ (H n (Nat.succ (Nat.succ k))) :=
      IsModuleTopology.toContinuousSMul (R := ℝ) (A := H n (Nat.succ (Nat.succ k)))
    exact IsModuleTopology.continuous_of_linearMap (R := ℝ) (A := H n (Nat.succ (Nat.succ (Nat.succ k))))
      (B := H n (Nat.succ (Nat.succ k))) (csl_pderivLM n k i)

private lemma csl_deriv_mem_closure (n k : ℕ) (i : Fin n) (g : H n (Nat.succ (Nat.succ (Nat.succ k))))
    (hg : g ∈ closure (Ŀ n (Nat.succ (Nat.succ (Nat.succ k))))) :
    ⟨g.1.pderiv i, g.2.pderiv⟩ ∈ closure (Ŀ n (Nat.succ (Nat.succ k))) := by
  let pfun : H n (Nat.succ (Nat.succ (Nat.succ k))) → H n (Nat.succ (Nat.succ k)) :=
    fun x => (⟨x.1.pderiv i, x.2.pderiv⟩ : H n (Nat.succ (Nat.succ k)))
  have hp : Continuous pfun := by
    change Continuous (csl_pderivCLM n k i)
    exact (csl_pderivCLM n k i).continuous
  have himg : pfun '' closure (Ŀ n (Nat.succ (Nat.succ (Nat.succ k)))) ⊆
      closure (pfun '' Ŀ n (Nat.succ (Nat.succ (Nat.succ k)))) :=
    image_closure_subset_closure_image hp
  have hpcl : pfun g ∈ closure (pfun '' Ŀ n (Nat.succ (Nat.succ (Nat.succ k)))) := himg ⟨g, hg, rfl⟩
  have hsub : pfun '' Ŀ n (Nat.succ (Nat.succ (Nat.succ k))) ⊆ Ŀ n (Nat.succ (Nat.succ k)) := by
    rintro h ⟨x, hx, rfl⟩
    simpa [Ŀ] using hx.2 i
  exact closure_mono hsub hpcl

private lemma csl_closure_nonneg (n d : ℕ) (g : H n d) (hg : g ∈ closure (Ŀ n d)) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ g.1.coeff m := by
  have hP : g ∈ closure (P n d) := closure_mono (csl_Ŀ_subset_P n d) hg
  rw [closure_P_eq_nonneg] at hP
  exact hP

private theorem csl_closure_subset_L_with
    (hRayL : ∀ (n d : ℕ), 0 < n → 2 ≤ d → ∀ f : H n d, f ∈ L n d →
      csl_RayCondPoly ((2 : ℝ) * (1 - 1 / (d : ℝ))) f.1)
    (hMRay : ∀ (n d : ℕ) (c : ℝ), 0 < c → ∀ (p : MvPolynomial (Fin n) ℝ),
      (∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) → p.IsHomogeneous d →
      csl_RayCondPoly c p → IsMConvex (p.support : Set (Fin n →₀ ℕ)))
    (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) ⊆ L n d := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro f hf
      cases d with
      | zero =>
          rw [show L n 0 = S n 0 by rfl]
          have hS : closure (P n 0) ⊆ S n 0 := by
            rw [closure_P_eq_S_of_degree_le_one n 0 (by norm_num)]
          exact hS hf
      | succ d0 =>
          cases d0 with
          | zero =>
              rw [show L n 1 = S n 1 by rfl]
              have hS : closure (P n 1) ⊆ S n 1 := by
                rw [closure_P_eq_S_of_degree_le_one n 1 (by norm_num)]
              exact hS hf
          | succ d1 =>
              cases d1 with
              | zero =>
                  rw [show L n 2 = S n 2 by rfl]
                  have hsub : Ŀ n 2 ⊆ S n 2 := strict_lorentzian_quadratic_subset_S n
                  have hclosed : IsClosed (S n 2) := S_closed n 2
                  have hcl : closure (Ŀ n 2) ⊆ S n 2 := by
                    calc
                      closure (Ŀ n 2) ⊆ closure (S n 2) := closure_mono hsub
                      _ = S n 2 := hclosed.closure_eq
                  exact hcl hf
              | succ k =>
                  dsimp [L]
                  constructor
                  · constructor
                    · let e : ℕ := Nat.succ (Nat.succ (Nat.succ k))
                      let c : ℝ := (2 : ℝ) * (1 - 1 / (e : ℝ))
                      have he3 : 3 ≤ e := by dsimp [e]; omega
                      have he2 : 2 ≤ e := by omega
                      have hcpos : 0 < c := by
                        dsimp [c]
                        have heR : (0 : ℝ) < (e : ℝ) := by
                          exact_mod_cast (by dsimp [e]; omega : 0 < e)
                        have heR1 : (1 : ℝ) < (e : ℝ) := by
                          exact_mod_cast (by dsimp [e]; omega : 1 < e)
                        have h1 : 1 - 1 / (e : ℝ) > 0 := by
                          rw [show 1 - 1 / (e : ℝ) = ((e : ℝ) - 1) / (e : ℝ) by
                            field_simp [heR.ne']]
                          exact div_pos (by linarith) heR
                        exact mul_pos (by norm_num) h1
                      have hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m :=
                        csl_closure_nonneg n (Nat.succ (Nat.succ (Nat.succ k))) f hf
                      have hclosedRay : IsClosed (csl_RayCondSet n (Nat.succ (Nat.succ (Nat.succ k))) c) :=
                        csl_isClosed_RayCondSet n (Nat.succ (Nat.succ (Nat.succ k))) c
                      have hsubRay : Ŀ n (Nat.succ (Nat.succ (Nat.succ k))) ⊆
                          csl_RayCondSet n (Nat.succ (Nat.succ (Nat.succ k))) c := by
                        intro g hg
                        have hgL : g ∈ L n (Nat.succ (Nat.succ (Nat.succ k))) :=
                          strict_subset_L n (Nat.succ (Nat.succ (Nat.succ k))) hn hg
                        have hR := hRayL n (Nat.succ (Nat.succ (Nat.succ k))) hn he2 g hgL
                        dsimp [csl_RayCondSet]
                        simpa [c, e] using hR
                      have hclRay : closure (Ŀ n (Nat.succ (Nat.succ (Nat.succ k)))) ⊆
                          csl_RayCondSet n (Nat.succ (Nat.succ (Nat.succ k))) c :=
                        closure_minimal hsubRay hclosedRay
                      have hfRay : csl_RayCondPoly c f.1 := by
                        exact hclRay hf
                      have hM := hMRay n (Nat.succ (Nat.succ (Nat.succ k))) c hcpos f.1 hnn f.2 hfRay
                      simpa using hM
                    · exact csl_closure_nonneg n (Nat.succ (Nat.succ (Nat.succ k))) f hf
                  · intro i
                    have hder : ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ closure (Ŀ n (Nat.succ (Nat.succ k))) :=
                      csl_deriv_mem_closure n k i f hf
                    have ihk : closure (Ŀ n (Nat.succ (Nat.succ k))) ⊆ L n (Nat.succ (Nat.succ k)) :=
                      ih (Nat.succ (Nat.succ k)) (by omega)
                    exact ihk hder
/-- The requested theorem: closure of the strictly Lorentzian polynomials is contained in the
Lorentzian polynomials. -/
theorem closure_subset_L (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) ⊆ L n d := by
  exact csl_closure_subset_L_with
    (fun n0 d0 hn0 hd0 f hf => L_subset_Rayleigh n0 d0 hn0 hd0 f hf)
    (fun n0 d0 c hc p hnn hhom hr =>
      Commons.Combinatorics.MvPolynomial.support_MConvex_of_homogeneous_Rayleigh n0 d0 c hc p hnn hhom hr)
    n d hn

end
end Commons.LorentzianPolynomials
