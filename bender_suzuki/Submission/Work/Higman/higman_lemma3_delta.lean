/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 3: the conjugation derivation `δ_u`

For a Suzuki 2-group `P`, a normal abelian `ξ`-invariant subgroup `A` and `u` in a normal
subgroup `C ≥ A` with `C² ≤ A²` (so in particular `[u,a] ∈ A²` for `a ∈ A`), the map
`δ_u(a) = a⁻¹ u⁻¹ a u = ⁅u,a⁆` is an endomorphism of `A` with image in `A²`; together with
`u^{-1} a u = a δ_u(a)` this is the "unipotent" description of conjugation by `u` used in
Higman's proof of Lemma 3 (`u^{-1}au = a^{1-2ν}`, `4(ν-ν²) = 0`).
-/
import Mathlib
import Submission.Work.Higman.higman_lemma3_base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]
variable {A C : Subgroup P}

/-- Abelian conjugation. -/
lemma conj_eq_of_abelian (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {x y : P} (hx : x ∈ A) (hy : y ∈ A) : x * y * x⁻¹ = y := by
  rw [hAb x hx y hy]; group

/-- Abelian inverse conjugation. -/
lemma inv_conj_eq_of_abelian (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {x y : P} (hx : x ∈ A) (hy : y ∈ A) : x⁻¹ * y * x = y := by
  rw [hAb x⁻¹ (A.inv_mem hx) y hy]; group

/-- Conjugation by `u⁻¹` on `A`. -/
noncomputable def sigmaA (hAn : A.Normal) (u : ↥C) (a : ↥A) : ↥A :=
  ⟨(u : P)⁻¹ * (a : P) * (u : P), by
    have h := hAn.conj_mem (a : P) a.2 (u : P)⁻¹
    simpa only [inv_inv, mul_assoc] using h⟩

/-- The derivation `a ↦ a⁻¹ u⁻¹ a u`. -/
noncomputable def deltaA (hAn : A.Normal) (u : ↥C) (a : ↥A) : ↥A :=
  ⟨(a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P))), by
    refine A.mul_mem (A.inv_mem a.2) ?_
    have h := hAn.conj_mem (a : P) a.2 (u : P)⁻¹
    simpa only [inv_inv, mul_assoc] using h⟩

@[simp] lemma sigmaA_coe (hAn : A.Normal) (u : ↥C) (a : ↥A) :
    ((sigmaA hAn u a : ↥A) : P) = (u : P)⁻¹ * (a : P) * (u : P) := rfl

@[simp] lemma deltaA_coe (hAn : A.Normal) (u : ↥C) (a : ↥A) :
    ((deltaA hAn u a : ↥A) : P) = (a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P))) := rfl

lemma mul_deltaA (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (u : ↥C) (a : ↥A) : a * deltaA hAn u a = sigmaA hAn u a := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, sigmaA_coe, deltaA_coe]
  group

lemma deltaA_one (hAn : A.Normal) (u : ↥C) : deltaA hAn u 1 = 1 := by
  apply Subtype.ext
  simp

lemma deltaA_mul (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (u : ↥C) (a b : ↥A) :
    deltaA hAn u (a * b) = deltaA hAn u a * deltaA hAn u b := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, deltaA_coe]
  have hX : (a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P))) ∈ A := (deltaA hAn u a).2
  have hb : ((b : P))⁻¹ ∈ A := A.inv_mem b.2
  have hcomm : (b : P)⁻¹ * ((a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P))))
      = ((a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P)))) * (b : P)⁻¹ :=
    hAb _ hb _ hX
  calc ((a : P) * (b : P))⁻¹ * ((u : P)⁻¹ * ((a : P) * (b : P) * (u : P)))
      = (b : P)⁻¹ * ((a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P))))
          * ((u : P)⁻¹ * ((b : P) * (u : P))) := by group
    _ = ((a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P)))) * (b : P)⁻¹
          * ((u : P)⁻¹ * ((b : P) * (u : P))) := by rw [hcomm]
    _ = ((a : P)⁻¹ * ((u : P)⁻¹ * ((a : P) * (u : P))))
          * ((b : P)⁻¹ * ((u : P)⁻¹ * ((b : P) * (u : P)))) := by group

lemma deltaA_mem_powSub_two (h : IsSuzuki2Grp P) (hA : IsXiAbelNormal h A) (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (u : ↥C) (a : ↥A) :
    ((deltaA hAn u a : ↥A) : P) ∈ powSub A 2 := by
  have hs : ⁅(u : P)⁻¹, (a : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h hA (u : P)⁻¹ (a : P) a.2
  have hsA : ⁅(u : P)⁻¹, (a : P)⁆ ∈ A := powSub_le (by norm_num : 0 < (2:ℕ)) hs
  have hd : ((deltaA hAn u a : ↥A) : P)
      = (a : P)⁻¹ * ⁅(u : P)⁻¹, (a : P)⁆ * (a : P) := by
    rw [deltaA_coe, commutatorElement_def]; group
  rw [hd]
  rw [inv_conj_eq_of_abelian hAb a.2 hsA]
  exact hs

lemma pow_two_mem_of_mem_sq {u : P} (huC : u ∈ C) (hC2 : powSub C 2 ≤ powSub A 2) :
    u ^ 2 ∈ A := by
  have h1 : u ^ 2 ∈ powSub C 2 := pow_mem_powSub huC
  exact powSub_le (by norm_num : 0 < (2:ℕ)) (hC2 h1)

lemma sigmaA_sq (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hC2 : powSub C 2 ≤ powSub A 2) (u : ↥C) (a : ↥A) :
    sigmaA hAn u (sigmaA hAn u a) = a := by
  have hu2 : (u : P) * (u : P) ∈ A := by
    rw [← pow_two]; exact pow_two_mem_of_mem_sq u.2 hC2
  apply Subtype.ext
  simp only [sigmaA_coe]
  have hkey : ((u : P) * (u : P))⁻¹ * (a : P) = (a : P) * ((u : P) * (u : P))⁻¹ :=
    hAb _ (A.inv_mem hu2) _ a.2
  rw [show (u : P)⁻¹ * ((u : P)⁻¹ * (a : P) * (u : P)) * (u : P)
      = ((u : P) * (u : P))⁻¹ * (a : P) * ((u : P) * (u : P)) from by group]
  rw [show ((u : P) * (u : P))⁻¹ * (a : P) * ((u : P) * (u : P))
      = (a : P) * ((u : P) * (u : P))⁻¹ * ((u : P) * (u : P)) from by rw [hkey]]
  group

lemma deltaA_eq_inv_mul_sigma (hAn : A.Normal) (u : ↥C) (b : ↥A) :
    deltaA hAn u b = b⁻¹ * sigmaA hAn u b := by
  apply Subtype.ext
  simp only [deltaA_coe, sigmaA_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  group

lemma deltaA_sigmaA (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hC2 : powSub C 2 ≤ powSub A 2) (u : ↥C) (a : ↥A) :
    deltaA hAn u (sigmaA hAn u a) = (deltaA hAn u a)⁻¹ := by
  rw [deltaA_eq_inv_mul_sigma hAn u (sigmaA hAn u a), sigmaA_sq hAn hAb hC2 u a,
    deltaA_eq_inv_mul_sigma hAn u a]
  group

lemma deltaA_deltaA (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hC2 : powSub C 2 ≤ powSub A 2) (u : ↥C) (a : ↥A) :
    deltaA hAn u (deltaA hAn u a) = (deltaA hAn u a)⁻¹ * (deltaA hAn u a)⁻¹ := by
  have h1 : deltaA hAn u (sigmaA hAn u a)
      = deltaA hAn u a * deltaA hAn u (deltaA hAn u a) := by
    rw [← mul_deltaA hAn hAb u a]
    exact deltaA_mul hAn hAb u a (deltaA hAn u a)
  rw [deltaA_sigmaA hAn hAb hC2 u a] at h1
  have h2 : (deltaA hAn u a)⁻¹ * (deltaA hAn u a)⁻¹ = deltaA hAn u (deltaA hAn u a) := by
    have := congrArg (fun x : ↥A => (deltaA hAn u a)⁻¹ * x) h1
    rw [inv_mul_cancel_left] at this
    exact this
  exact h2.symm

lemma sq_mul_eq (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (u : ↥C) (a : ↥A) :
    (u : P) * (a : P) * (u : P) * (a : P)
      = (u : P) * (u : P) * ((a : P) * (a : P) * (deltaA hAn u a : P)) := by
  have h2 : (a : P) * (deltaA hAn u a : P) = (sigmaA hAn u a : P) := by
    simpa using congrArg (fun x : ↥A => (x : P)) (mul_deltaA hAn hAb u a)
  have h3 : (a : P) * (a : P) * (deltaA hAn u a : P)
      = (sigmaA hAn u a : P) * (a : P) := by
    rw [mul_assoc, h2]
    exact hAb _ a.2 _ (sigmaA hAn u a).2
  calc (u : P) * (a : P) * (u : P) * (a : P)
      = (u : P) * (u : P) * ((sigmaA hAn u a : P) * (a : P)) := by rw [sigmaA_coe]; group
    _ = (u : P) * (u : P) * ((a : P) * (a : P) * (deltaA hAn u a : P)) := by rw [h3]


noncomputable def xiA (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a : ↥A) : ↥A :=
  ⟨h.xi a, by
    have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
    rwa [hAinv] at hm⟩

noncomputable def xiAinv (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a : ↥A) : ↥A :=
  ⟨(h.xi : MulAut P).symm a, symm_mem_of_map_eq h.xi hAinv a.2⟩

noncomputable def xiC (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) : ↥C :=
  ⟨h.xi u, by
    have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom u.2
    rwa [hCinv] at hm⟩

@[simp] lemma xiA_coe (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a : ↥A) :
    ((xiA h hAinv a : ↥A) : P) = h.xi (a : P) := rfl

@[simp] lemma xiAinv_coe (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A) (a : ↥A) :
    ((xiAinv h hAinv a : ↥A) : P) = (h.xi : MulAut P).symm (a : P) := rfl

@[simp] lemma xiC_coe (h : IsSuzuki2Grp P) {C : Subgroup P}
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) :
    ((xiC h hCinv u : ↥C) : P) = h.xi (u : P) := rfl

lemma deltaA_xi (h : IsSuzuki2Grp P) {A C : Subgroup P} (hAn : A.Normal)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) (a : ↥A) :
    deltaA hAn (xiC h hCinv u) a = xiA h hAinv (deltaA hAn u (xiAinv h hAinv a)) := by
  apply Subtype.ext
  show (a : P)⁻¹ * ((h.xi (u : P))⁻¹ * ((a : P) * h.xi (u : P)))
     = h.xi (((h.xi : MulAut P).symm (a : P))⁻¹
        * ((u : P)⁻¹ * ((h.xi : MulAut P).symm (a : P) * (u : P))))
  simp
  try group

lemma deltaA_mem_powSub_four_of_mem_powSub_two (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (u : ↥C) {c : P}
    (hcA : c ∈ A) (hc : c ∈ powSub A 2) :
    ((deltaA hAn u ⟨c, hcA⟩ : ↥A) : P) ∈ powSub A 4 := by
  obtain ⟨x, hx, rfl⟩ := (mem_powSub_iff hAb).mp hc
  have hsub : (⟨x ^ 2, hcA⟩ : ↥A) = ⟨x, hx⟩ * ⟨x, hx⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact pow_two x
  rw [hsub, deltaA_mul hAn hAb u ⟨x, hx⟩ ⟨x, hx⟩]
  have hd : ((deltaA hAn u ⟨x, hx⟩ : ↥A) : P) ∈ powSub A 2 :=
    deltaA_mem_powSub_two h hA hAn hAb u ⟨x, hx⟩
  have hsq : ((deltaA hAn u ⟨x, hx⟩ : ↥A) : P) ^ 2 ∈ powSub (powSub A 2) 2 :=
    pow_mem_powSub hd
  rw [powSub_powSub hAb 2 2] at hsq
  have hsq' : ((deltaA hAn u ⟨x, hx⟩ : ↥A) : P) * ((deltaA hAn u ⟨x, hx⟩ : ↥A) : P)
      ∈ powSub A 4 := by
    rw [← pow_two]; exact hsq
  simpa only [Subgroup.coe_mul] using hsq'


/-- `δ_{uv}(a) = δ_u(a) * δ_v(a) * δ_v(δ_u(a))` (the last factor lies in `A⁴`). -/
lemma deltaA_mul_uv (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (u v : ↥C) (a : ↥A) :
    deltaA hAn (u * v) a
      = deltaA hAn u a * deltaA hAn v a * deltaA hAn v (deltaA hAn u a) := by
  haveI : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun x y => Subtype.ext (hAb x x.2 y y.2) }
  have h1 : deltaA hAn (u * v) a = deltaA hAn u a * deltaA hAn v (sigmaA hAn u a) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, deltaA_coe, sigmaA_coe]
    group
  calc deltaA hAn (u * v) a
      = deltaA hAn u a * deltaA hAn v (sigmaA hAn u a) := h1
    _ = deltaA hAn u a * deltaA hAn v (a * deltaA hAn u a) := by
          rw [← mul_deltaA hAn hAb u a]
    _ = deltaA hAn u a * (deltaA hAn v a * deltaA hAn v (deltaA hAn u a)) := by
          rw [deltaA_mul hAn hAb v a (deltaA hAn u a)]
    _ = deltaA hAn u a * deltaA hAn v a * deltaA hAn v (deltaA hAn u a) := by group

end Work.Higman
