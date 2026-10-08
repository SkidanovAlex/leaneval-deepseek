import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.A_quot_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open scoped commutatorElement

/-- The elementary identity `(xy)² = x²y²·(y⁻¹[y⁻¹,x⁻¹]y)`. -/
theorem sq_mul_decomp {G : Type*} [Group G] (x y : G) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y) := by
  rw [commutatorElement_def, pow_two]; group

/-- If `A = Φ(C)` is a `ξ`-invariant abelian normal subgroup of a Suzuki 2-group, `C` is a
normal `ξ`-subgroup covering `A`, `C' ≤ A²`, and `2 ^ e` is the exponent of `A` (with
`powSub A (2 ^ (e-1)) = A ⊓ Ω₁`), then the map `x ↦ x ^ 2 ^ e` from `C` to `A ⊓ Ω₁` is a
homomorphism onto `A ⊓ Ω₁` with kernel `A`, commuting with `ξ`. -/
theorem higman_lemma7_phi2 {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A) (hCn : C.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A) (hCd : ⁅C, C⁆ ≤ Work.Higman.powSub A 2)
    (hAne : A ≠ ⊥) {e : ℕ} (he : 1 ≤ e) (h1 : ∀ x ∈ A, x ^ 2 ^ e = 1)
    (hkey : ∀ y ∈ A, y ∈ Work.Higman.powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1)
    (hker : Work.Higman.powSub A (2 ^ (e - 1)) = A ⊓ Work.Higman.omega1 P) :
    (∀ x ∈ C, ∀ y ∈ C, (x * y) ^ 2 ^ e = x ^ 2 ^ e * y ^ 2 ^ e) ∧
      (∀ x ∈ C, x ^ 2 ^ e ∈ A ⊓ Work.Higman.omega1 P) ∧
      (∀ w ∈ A ⊓ Work.Higman.omega1 P, ∃ x ∈ C, x ^ 2 ^ e = w) ∧
      (∀ x ∈ C, x ^ 2 ^ e = 1 ↔ x ∈ A) ∧
      (∀ x ∈ C, (h.xi x) ^ 2 ^ e = h.xi (x ^ 2 ^ e)) := by
  classical
  have hAb := hA.abelian
  have hAn := hA.normal
  have hsq_le_A : powSub C 2 ≤ A := by rw [← hPhi]; exact le_sup_left
  have hA2le : powSub A 2 ≤ A := powSub_le (by norm_num)
  have he1 : 2 * 2 ^ (e - 1) = 2 ^ e := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  have hA2normal : (powSub A 2).Normal :=
    Subgroup.Normal.mk (fun n hn g => by
      rw [mem_powSub_iff hAb] at hn ⊢
      obtain ⟨a, ha, rfl⟩ := hn
      exact ⟨g * a * g⁻¹, hAn.conj_mem a ha g, by simp only [pow_two]; group⟩)
  -- ### conjunct 1 : `x ↦ x ^ 2 ^ e` is a homomorphism on `C`
  have hhom : ∀ x ∈ C, ∀ y ∈ C, (x * y) ^ 2 ^ e = x ^ 2 ^ e * y ^ 2 ^ e := by
    intro x hx y hy
    have hx2A : x ^ 2 ∈ A := hsq_le_A (pow_mem_powSub hx)
    have hy2A : y ^ 2 ∈ A := hsq_le_A (pow_mem_powSub hy)
    have hd2 : y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y ∈ powSub A 2 := by
      have hc : ⁅y⁻¹, x⁻¹⁆ ∈ powSub A 2 :=
        hCd (Subgroup.commutator_mem_commutator (C.inv_mem hy) (C.inv_mem hx))
      have hconj := hA2normal.conj_mem ⁅y⁻¹, x⁻¹⁆ hc y⁻¹
      simpa using hconj
    have hdA : y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y ∈ A := hA2le hd2
    have hid : (x * y) ^ 2 = x ^ 2 * y ^ 2 * (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y) := sq_mul_decomp x y
    have hd1 : (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y) ^ 2 ^ (e - 1) = 1 := (hkey _ hdA).mp hd2
    have hpx : (x ^ 2) ^ 2 ^ (e - 1) = x ^ 2 ^ e := by rw [← pow_mul, he1]
    have hpy : (y ^ 2) ^ 2 ^ (e - 1) = y ^ 2 ^ e := by rw [← pow_mul, he1]
    have hc1 : Commute (x ^ 2) (y ^ 2) := by rw [Commute]; exact hAb _ hx2A _ hy2A
    have hc2 : Commute (x ^ 2 * y ^ 2) (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y) := by
      rw [Commute]; exact hAb _ (A.mul_mem hx2A hy2A) _ hdA
    calc (x * y) ^ 2 ^ e
        = ((x * y) ^ 2) ^ 2 ^ (e - 1) := by rw [← he1, pow_mul]
      _ = (x ^ 2 * y ^ 2 * (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y)) ^ 2 ^ (e - 1) := by rw [hid]
      _ = (x ^ 2) ^ 2 ^ (e - 1) * (y ^ 2) ^ 2 ^ (e - 1)
            * (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y) ^ 2 ^ (e - 1) := by
            rw [show x ^ 2 * y ^ 2 * (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y)
                  = (x ^ 2 * y ^ 2) * (y⁻¹ * ⁅y⁻¹, x⁻¹⁆ * y) from rfl]
            rw [Commute.mul_pow hc2, Commute.mul_pow hc1]
      _ = x ^ 2 ^ e * y ^ 2 ^ e := by rw [hd1, mul_one, hpx, hpy]
  -- ### conjunct 2 : the image lies in `A ⊓ Ω₁`
  have himg : ∀ x ∈ C, x ^ 2 ^ e ∈ A ⊓ omega1 P := by
    intro x hx
    have hx2A : x ^ 2 ∈ A := hsq_le_A (pow_mem_powSub hx)
    have hgoal : x ^ 2 ^ e = (x ^ 2) ^ 2 ^ (e - 1) := by rw [← he1, pow_mul]
    rw [hgoal, ← hker]
    exact pow_mem_powSub hx2A
  -- ### the homomorphism `φ`
  let φ : ↥C →* P :=
    { toFun := fun x => (x : P) ^ 2 ^ e
      map_one' := by simp
      map_mul' := fun x y => hhom x x.2 y y.2 }
  have hrange_le : φ.range ≤ A ⊓ omega1 P := by
    rintro w ⟨y, rfl⟩
    exact himg y y.2
  have hxiC : ∀ y : P, y ∈ C → h.xi y ∈ C := by
    intro y hy
    have hmem := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) hy
    rwa [hCinv] at hmem
  have hxiCinv : ∀ y : P, y ∈ C → (h.xi : MulAut P).symm y ∈ C := by
    intro y hy
    have hy' : y ∈ C.map (h.xi : MulAut P).toMonoidHom := by rw [hCinv]; exact hy
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : (h.xi : MulAut P).symm y = z := by rw [← hzy]; simp
    rwa [hzy']
  have hmap_xi : ∀ z : ↥C,
      (h.xi : MulAut P).toMonoidHom (φ z) = φ ⟨h.xi z, hxiC z z.2⟩ := by
    intro z
    show (h.xi : MulAut P).toMonoidHom ((z : P) ^ 2 ^ e) = ((h.xi (z : P) : P) ^ 2 ^ e)
    exact map_pow (h.xi : MulAut P).toMonoidHom (z : P) (2 ^ e)
  have hmap_xi_inv : ∀ z : ↥C,
      (h.xi : MulAut P).toMonoidHom (φ ⟨(h.xi : MulAut P).symm (z : P), hxiCinv z z.2⟩)
        = φ z := by
    intro z
    show (h.xi : MulAut P).toMonoidHom (((h.xi : MulAut P).symm (z : P)) ^ 2 ^ e)
        = ((z : P) ^ 2 ^ e)
    rw [map_pow]
    congr 1
    rw [MulEquiv.toMonoidHom_eq_coe]; exact MulEquiv.apply_symm_apply (h.xi : MulAut P) (z : P)
  have hrange_inv : φ.range.map (h.xi : MulAut P).toMonoidHom = φ.range := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      rw [Subgroup.mem_comap]
      obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [hmap_xi z]
      exact ⟨⟨h.xi z, hxiC z z.2⟩, rfl⟩
    · intro y hy
      obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
      have hmem : φ ⟨(h.xi : MulAut P).symm (z : P), hxiCinv z z.2⟩ ∈ φ.range := ⟨_, rfl⟩
      have hconj := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) hmem
      rwa [hmap_xi_inv z] at hconj
  -- ### the kernel subgroup `D`
  let D : Subgroup P := φ.ker.map C.subtype
  have hDle : D ≤ C := by
    intro y hy
    obtain ⟨z, -, hzy⟩ := Subgroup.mem_map.mp hy
    rw [← hzy]; exact z.2
  have hAD : A ≤ D := by
    intro a ha
    refine Subgroup.mem_map.mpr ⟨⟨a, hAC ha⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    exact h1 a ha
  have hDchar : ∀ (x : P) (hx : x ∈ C), x ∈ D ↔ x ^ 2 ^ e = 1 := by
    intro x hx
    constructor
    · intro hxD
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxD
      rw [MonoidHom.mem_ker] at hz
      have hzx' : (⟨x, hx⟩ : ↥C) = z := Subtype.ext hzx.symm
      have : φ ⟨x, hx⟩ = 1 := by rw [hzx']; exact hz
      exact this
    · intro hxe
      refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      exact hxe
  have hDnormal : D.Normal :=
    Subgroup.Normal.mk (fun y hy g => by
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      rw [MonoidHom.mem_ker] at hz
      have hyC : y ∈ C := hzy ▸ z.2
      have hconjC : g * y * g⁻¹ ∈ C := hCn.conj_mem y hyC g
      refine Subgroup.mem_map.mpr ⟨⟨g * y * g⁻¹, hconjC⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      have hy2 : y ^ 2 ^ e = 1 := by rw [← hzy]; exact hz
      show (g * y * g⁻¹) ^ 2 ^ e = 1
      rw [show g * y * g⁻¹ = (MulAut.conj g) y from by rw [MulAut.conj_apply],
        ← map_pow, hy2, map_one])
  have hDinv : D.map (h.xi : MulAut P).toMonoidHom = D := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      rw [Subgroup.mem_comap]
      have hyC : y ∈ C := hDle hy
      have hxyC : (h.xi : MulAut P).toMonoidHom y ∈ C := hxiC y hyC
      rw [hDchar ((h.xi : MulAut P).toMonoidHom y) hxyC]
      have hye : y ^ 2 ^ e = 1 := (hDchar y hyC).mp hy
      show (h.xi : MulAut P).toMonoidHom y ^ 2 ^ e = 1
      rw [← map_pow, hye, map_one]
    · intro y hy
      have hyC : y ∈ C := hDle hy
      have hziC : (h.xi : MulAut P).symm y ∈ C := hxiCinv y hyC
      have hziD : (h.xi : MulAut P).symm y ∈ D := by
        rw [hDchar _ hziC]
        have hye : y ^ 2 ^ e = 1 := (hDchar y hyC).mp hy
        show ((h.xi : MulAut P).symm y) ^ 2 ^ e = 1
        rw [← map_pow, hye, map_one]
      have hmem := Subgroup.mem_map_of_mem (f := (h.xi : MulAut P).toMonoidHom) hziD
      have hyy : (h.xi : MulAut P).toMonoidHom ((h.xi : MulAut P).symm y) = y := by
        rw [MulEquiv.toMonoidHom_eq_coe]; exact MulEquiv.apply_symm_apply (h.xi : MulAut P) y
      rwa [hyy] at hmem
  have hDcover : D = A ∨ D = C := hcover D hDnormal hDinv hAD hDle
  have hDne : D ≠ C := by
    intro hDC
    have hC2le : powSub C 2 ≤ powSub A 2 := by
      rw [powSub, Subgroup.closure_le]
      rintro s ⟨x, hx, rfl⟩
      have hx2A : x ^ 2 ∈ A := hsq_le_A (pow_mem_powSub hx)
      have hxe : x ^ 2 ^ e = 1 := (hDchar x hx).mp (hDC ▸ hx)
      refine (hkey (x ^ 2) hx2A).mpr ?_
      rw [← pow_mul, he1]; exact hxe
    have hAle : A ≤ powSub A 2 :=
      calc A = powSub C 2 ⊔ ⁅C, C⁆ := hPhi.symm
        _ ≤ powSub A 2 := sup_le hC2le hCd
    have hAeq : powSub A 2 = A := le_antisymm hA2le hAle
    have hsurj : ∀ n, ∀ x ∈ A, ∃ s ∈ A, s ^ 2 ^ n = x := by
      intro n
      induction n with
      | zero => intro x hx; exact ⟨x, hx, by rw [pow_zero, pow_one]⟩
      | succ n ih =>
        intro x hx
        obtain ⟨t, ht, ht2⟩ := (mem_powSub_iff hAb).mp (hAeq ▸ hx)
        obtain ⟨s, hs, hs2⟩ := ih t ht
        exact ⟨s, hs, by rw [pow_succ, pow_mul, hs2, ht2]⟩
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAne
    obtain ⟨s, hs, hsx⟩ := hsurj e (x : P) x.2
    have hxtriv : (x : P) = 1 := by rw [← hsx]; exact h1 s hs
    exact hx1 (Subtype.ext hxtriv)
  have hDA : D = A := hDcover.resolve_right hDne
  -- ### conjunct 3 : surjectivity, from irreducibility of `A ⊓ Ω₁`
  have hrange_eq : φ.range = A ⊓ omega1 P := by
    rcases invariant_subgroup_inf_omega1 h A hrange_le hrange_inv with hbot | htop
    · exfalso
      have hCle : C ≤ D := by
        intro x hx
        have hmem0 : φ ⟨x, hx⟩ = 1 := by
          have h : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
          rw [hbot] at h
          simpa using h
        rw [hDchar x hx]
        exact hmem0
      have hCD : C = D := le_antisymm hCle hDle
      rw [hDA] at hCD
      exact hCA hCD.symm
    · exact htop
  -- ### conjunct 5 : commutation with `ξ`
  have hxi_comm : ∀ x ∈ C, (h.xi x) ^ 2 ^ e = h.xi (x ^ 2 ^ e) := by
    intro x hx
    exact (map_pow (h.xi : MulAut P).toMonoidHom x (2 ^ e)).symm
  refine ⟨hhom, himg, ?_, ?_, hxi_comm⟩
  · intro w hw
    have hw' : w ∈ φ.range := by rw [hrange_eq]; exact hw
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hw'
    exact ⟨(z : P), z.2, hz⟩
  · intro x hx
    constructor
    · intro hxe
      have : x ∈ D := (hDchar x hx).mpr hxe
      rw [hDA] at this
      exact this
    · intro hxA
      exact h1 x hxA

end Work.Higman
