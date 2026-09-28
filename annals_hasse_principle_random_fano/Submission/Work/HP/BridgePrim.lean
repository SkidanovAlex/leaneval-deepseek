import Mathlib
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.IsPrimBasic
import Submission.Work.HP.BridgeEval
import Submission.Work.HP.BridgeAux.height_formOf
import Submission.Work.HP.BridgeAux.prim_eq_or_eq_neg

/-!
# Primitive coefficient vectors of homogeneous forms

For a non-zero homogeneous rational form `f` of degree `d` we construct the primitive integer
coefficient vector `primVec f` (clear the denominators of the coefficients and divide by the gcd
of the numerators, exactly as in the challenge's `height`).  It satisfies

* `formOf d n (primVec f) = c • f` for the non-zero rational `c = D / G`,
* `IsPrim (primVec f)`,
* `height f = eNorm (primVec f)`.

Consequently every projective point has a primitive coefficient vector (`toV_surjective`), the
primitive vector is unique up to sign (`toV_eq_toV`), and the height of any representative of a
projective point is the norm of that primitive vector (`height_rep`).
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset
open scoped LinearAlgebra.Projectivization

namespace Work.HP

variable {d n : ℕ}

/-! ## Degree-`d` exponent vectors -/

/-- The monomial index attached to an exponent vector of total degree `d`. -/
def Mon.ofFinsupp (s : Fin (n + 1) →₀ ℕ) (hs : Finsupp.degree s = d) : Mon d n :=
  ⟨fun i => ⟨s i, by have := Finsupp.le_degree i s; omega⟩, by
    simp only [Fin.val_mk]
    rw [← Finsupp.degree_eq_sum]
    exact hs⟩

@[simp] lemma Mon.toFinsupp_ofFinsupp (s : Fin (n + 1) →₀ ℕ) (hs : Finsupp.degree s = d) :
    Mon.toFinsupp (Mon.ofFinsupp s hs) = s := by
  ext i
  rw [Mon_toFinsupp_apply]
  rfl

lemma IsHomogeneous.degree_eq {f : MvPolynomial (Fin (n + 1)) ℚ} (hhom : f.IsHomogeneous d)
    {s : Fin (n + 1) →₀ ℕ} (hs : s ∈ f.support) : Finsupp.degree s = d := by
  have h := hhom (mem_support_iff.mp hs)
  simpa [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, Pi.one_apply] using h

lemma exists_mon_of_mem_support {f : MvPolynomial (Fin (n + 1)) ℚ} (hhom : f.IsHomogeneous d)
    {s : Fin (n + 1) →₀ ℕ} (hs : s ∈ f.support) : ∃ m : Mon d n, Mon.toFinsupp m = s :=
  ⟨Mon.ofFinsupp s (IsHomogeneous.degree_eq (d := d) hhom hs), Mon.toFinsupp_ofFinsupp s _⟩

/-- Coefficients of `formOf` at exponent vectors that are not degree-`d` monomials vanish. -/
lemma formOf_coeff_eq_zero (a : Mon d n → ℤ) {s : Fin (n + 1) →₀ ℕ}
    (hs : ∀ m : Mon d n, Mon.toFinsupp m ≠ s) : (formOf d n a).coeff s = 0 := by
  rw [formOf, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [MvPolynomial.coeff_monomial]
  exact if_neg (hs m)

lemma formOf_neg (d n : ℕ) (a : Mon d n → ℤ) : formOf d n (-a) = -formOf d n a := by
  simp only [formOf, Pi.neg_apply, Int.cast_neg]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun m _ => by simp


lemma IsPrim.neg {v : Mon d n → ℤ} (h : IsPrim v) : IsPrim (-v) := (IsPrim_neg v).2 h

/-! ## The primitive vector of a homogeneous form -/

/-- The lcm of the denominators of the coefficients of `f`. -/
def clearance (f : MvPolynomial (Fin (n + 1)) ℚ) : ℕ :=
  f.support.lcm fun s => (f.coeff s).den

/-- The numerator of the coefficient at `s` after clearing denominators. -/
def clearNum (f : MvPolynomial (Fin (n + 1)) ℚ) (s : Fin (n + 1) →₀ ℕ) : ℤ :=
  (clearance f * f.coeff s).num

/-- The gcd of the clearing numerators over the support of `f`. -/
def clearGcd (f : MvPolynomial (Fin (n + 1)) ℚ) : ℤ := f.support.gcd (clearNum f)

/-- The primitive integer coefficient vector of the form `f`. -/
def primVec (f : MvPolynomial (Fin (n + 1)) ℚ) : Mon d n → ℤ :=
  fun m => clearNum f (Mon.toFinsupp m) / clearGcd f

lemma clearance_ne_zero {f : MvPolynomial (Fin (n + 1)) ℚ} (hf : f ≠ 0) : clearance f ≠ 0 := by
  intro h
  rw [clearance, Finset.lcm_eq_zero_iff] at h
  obtain ⟨s, hs, hden⟩ := h
  exact (f.coeff s).den_nz hden

/-- Clearing the denominators of a rational is exact. -/
lemma num_mul_den (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ((D * q).num : ℚ) = (D : ℚ) * q := by
  set A : ℤ := ((D / q.den : ℕ) : ℤ) * q.num with hA
  have hdenq : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
  have hD : ((D / q.den : ℕ) : ℚ) * (q.den : ℚ) = (D : ℚ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel h]
  have hval : (D : ℚ) * q = (A : ℚ) := by
    rw [hA]
    rw [show ((((D / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ)
        = ((D / q.den : ℕ) : ℚ) * (q.num : ℚ) from by
      rw [Int.cast_mul, Int.cast_natCast]]
    rw [← hdenq, ← hD]
    ring
  have hnum : (D * q).num = A := by
    have h2 := congrArg Rat.num hval
    rwa [Rat.num_intCast] at h2
  rw [hnum, ← hval]

lemma clearNum_cast (f : MvPolynomial (Fin (n + 1)) ℚ) (s : Fin (n + 1) →₀ ℕ) :
    ((clearNum f s : ℤ) : ℚ) = (clearance f : ℚ) * f.coeff s := by
  by_cases hs : s ∈ f.support
  · exact num_mul_den (f.coeff s) (clearance f) (by
      rw [clearance]; exact Finset.dvd_lcm hs)
  · have hc : f.coeff s = 0 := by simpa [mem_support_iff] using hs
    rw [clearNum, hc, mul_zero]
    simp

lemma clearGcd_dvd_of_coeff (f : MvPolynomial (Fin (n + 1)) ℚ) (s : Fin (n + 1) →₀ ℕ) :
    clearGcd f ∣ clearNum f s := by
  by_cases hs : s ∈ f.support
  · exact Finset.gcd_dvd hs
  · have hc : f.coeff s = 0 := by simpa [mem_support_iff] using hs
    rw [clearNum, hc, mul_zero]
    exact dvd_zero _

lemma clearGcd_ne_zero {f : MvPolynomial (Fin (n + 1)) ℚ} (hf : f ≠ 0) : clearGcd f ≠ 0 := by
  intro h
  rw [clearGcd, Finset.gcd_eq_zero_iff] at h
  apply hf
  ext s
  by_cases hs : s ∈ f.support
  · have h1 : (clearance f : ℚ) * f.coeff s = 0 := by
      have h2 := h s hs
      have h3 := clearNum_cast f s
      rw [h2] at h3
      exact h3.symm
    have hD : (clearance f : ℚ) ≠ 0 := by
      exact_mod_cast clearance_ne_zero hf
    exact (mul_eq_zero.1 h1).resolve_left hD
  · simpa [mem_support_iff] using hs

/-- The support of a non-zero homogeneous form is the image of the monomials whose clearing
numerator does not vanish. -/
lemma support_eq_image (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f ≠ 0)
    (hhom : f.IsHomogeneous d) :
    f.support = (Finset.univ.filter fun m : Mon d n => clearNum f (Mon.toFinsupp m) ≠ 0).image
      Mon.toFinsupp := by
  classical
  have hD : (clearance f : ℚ) ≠ 0 := by exact_mod_cast clearance_ne_zero hf
  ext s
  constructor
  · intro hs
    obtain ⟨m, hm⟩ := exists_mon_of_mem_support (d := d) hhom hs
    have hmf : clearNum f (Mon.toFinsupp m) ≠ 0 := by
      intro h0
      have h1 : ((clearNum f (Mon.toFinsupp m) : ℤ) : ℚ)
          = (clearance f : ℚ) * f.coeff (Mon.toFinsupp m) := clearNum_cast f _
      rw [h0] at h1
      have h2 : (clearance f : ℚ) * f.coeff (Mon.toFinsupp m) = 0 := by simpa using h1.symm
      have h3 : f.coeff (Mon.toFinsupp m) = 0 := (mul_eq_zero.1 h2).resolve_left hD
      rw [hm] at h3
      exact (mem_support_iff.mp hs) h3
    exact Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨Finset.mem_univ m, hmf⟩, hm⟩
  · intro hmem
    obtain ⟨m, hm, hms⟩ := Finset.mem_image.1 hmem
    rw [Finset.mem_filter] at hm
    rw [mem_support_iff, ← hms]
    intro h0
    exact hm.2 (by rw [clearNum, h0, mul_zero]; rfl)

lemma formOf_primVec (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f ≠ 0)
    (hhom : f.IsHomogeneous d) :
    formOf d n (primVec (d := d) f) = ((clearance f : ℚ) / (clearGcd f : ℚ)) • f := by
  have hG : (clearGcd f : ℚ) ≠ 0 := by exact_mod_cast clearGcd_ne_zero hf
  ext s
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hs : ∃ m : Mon d n, Mon.toFinsupp m = s
  · obtain ⟨m, rfl⟩ := hs
    simp only [primVec, formOf_coeff]
    have hdvd : clearGcd f ∣ clearNum f (Mon.toFinsupp m) := clearGcd_dvd_of_coeff f _
    have hmul : (clearGcd f : ℚ)
        * ((clearNum f (Mon.toFinsupp m) / clearGcd f : ℤ) : ℚ)
        = (clearNum f (Mon.toFinsupp m) : ℚ) := by
      have h1 : clearGcd f * (clearNum f (Mon.toFinsupp m) / clearGcd f)
          = clearNum f (Mon.toFinsupp m) := by
        rw [mul_comm, Int.ediv_mul_cancel hdvd]
      rw [← Int.cast_mul, h1]
    have hA : ((clearNum f (Mon.toFinsupp m) / clearGcd f : ℤ) : ℚ)
        = (clearNum f (Mon.toFinsupp m) : ℚ) / (clearGcd f : ℚ) := by
      rw [eq_div_iff hG]
      rw [mul_comm]
      exact hmul
    rw [hA, clearNum_cast f (Mon.toFinsupp m), div_mul_eq_mul_div]
  · have hzero : ∀ m : Mon d n, Mon.toFinsupp m ≠ s := fun m h => hs ⟨m, h⟩
    have hcoeff0 : f.coeff s = 0 := by
      by_contra hc
      exact hs (exists_mon_of_mem_support (d := d) hhom (mem_support_iff.mpr hc))
    rw [formOf_coeff_eq_zero (primVec (d := d) f) hzero, hcoeff0]
    simp

lemma IsPrim_primVec (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f ≠ 0)
    (hhom : f.IsHomogeneous d) : IsPrim (primVec (d := d) f) := by
  classical
  have hG : clearGcd f ≠ 0 := clearGcd_ne_zero hf
  have hwit : ∃ s ∈ f.support, clearNum f s ≠ 0 := by
    have h : clearGcd f ≠ 0 := hG
    rw [clearGcd] at h
    exact Finset.gcd_ne_zero_iff.mp h
  obtain ⟨s₀, hs₀, hnum₀⟩ := hwit
  have hsupp : f.support.gcd (fun s => clearNum f s / clearGcd f) = 1 :=
    Finset.gcd_div_eq_one (s := f.support) (f := clearNum f) hs₀ hnum₀
  unfold IsPrim
  have hdvd1 : Finset.univ.gcd (fun m : Mon d n => clearNum f (Mon.toFinsupp m) / clearGcd f)
      ∣ f.support.gcd (fun s => clearNum f s / clearGcd f) := by
    refine Finset.dvd_gcd (s := f.support)
      (f := fun s : Fin (n + 1) →₀ ℕ => clearNum f s / clearGcd f) ?_
    intro s hs
    obtain ⟨m, hm⟩ := exists_mon_of_mem_support (d := d) hhom hs
    rw [← hm]
    exact Finset.gcd_dvd (Finset.mem_univ m)
  have hdvd2 : f.support.gcd (fun s => clearNum f s / clearGcd f)
      ∣ Finset.univ.gcd (fun m : Mon d n => clearNum f (Mon.toFinsupp m) / clearGcd f) := by
    refine Finset.dvd_gcd (s := (Finset.univ : Finset (Mon d n)))
      (f := fun m : Mon d n => clearNum f (Mon.toFinsupp m) / clearGcd f) ?_
    intro m _
    by_cases hm : Mon.toFinsupp m ∈ f.support
    · exact Finset.gcd_dvd hm
    · have hc : clearNum f (Mon.toFinsupp m) = 0 := by
        have h0 : f.coeff (Mon.toFinsupp m) = 0 := by simpa [mem_support_iff] using hm
        rw [clearNum, h0, mul_zero]
        rfl
      rw [hc]
      simp
  have h1 : Finset.univ.gcd (fun m : Mon d n => clearNum f (Mon.toFinsupp m) / clearGcd f)
      ∣ (1 : ℤ) := hsupp ▸ hdvd1
  have h2 : (1 : ℤ)
      ∣ Finset.univ.gcd (fun m : Mon d n => clearNum f (Mon.toFinsupp m) / clearGcd f) :=
    hsupp ▸ hdvd2
  have hnn : 0 ≤ (Finset.univ : Finset (Mon d n)).gcd
      (fun m : Mon d n => clearNum f (Mon.toFinsupp m) / clearGcd f) :=
    Finset.Int.finsetGcd_nonneg
  exact Int.dvd_antisymm hnn (by norm_num) h1 h2

lemma height_primVec (f : MvPolynomial (Fin (n + 1)) ℚ) (hf : f ≠ 0)
    (hhom : f.IsHomogeneous d) :
    HassePrincipleRandomFano.height f = eNorm (primVec (d := d) f) := by
  classical
  have hheight : HassePrincipleRandomFano.height f
      = Real.sqrt (∑ s ∈ f.support, (((clearNum f s / clearGcd f : ℤ)) : ℝ) ^ 2) := by
    unfold HassePrincipleRandomFano.height
    rfl
  have hsum_gen : ∀ (g : (Fin (n + 1) →₀ ℕ) → ℝ),
      (∀ s, clearNum f s = 0 → g s = 0) →
      (∑ s ∈ f.support, g s) = ∑ m : Mon d n, g (Mon.toFinsupp m) := by
    intro g hg0
    rw [support_eq_image (d := d) f hf hhom]
    rw [Finset.sum_image (s := Finset.univ.filter
        (fun m : Mon d n => clearNum f (Mon.toFinsupp m) ≠ 0))
      (g := Mon.toFinsupp) (f := g)
      (fun x _ y _ h => Mon_toFinsupp_injective h)]
    refine Finset.sum_subset (Finset.filter_subset (s := Finset.univ)
      (p := fun m : Mon d n => clearNum f (Mon.toFinsupp m) ≠ 0)) ?_
    intro m _ hm
    have hc : clearNum f (Mon.toFinsupp m) = 0 := by
      by_contra hc
      exact hm (Finset.mem_filter.2 ⟨Finset.mem_univ m, hc⟩)
    exact hg0 _ hc
  have hsum := hsum_gen (fun s : Fin (n + 1) →₀ ℕ =>
    (((clearNum f s / clearGcd f : ℤ)) : ℝ) ^ 2) (by
      intro s hs
      rw [hs]
      simp)
  rw [hheight, eNorm, hsum]
  congr 1

/-- Every non-zero homogeneous rational form has a primitive integer coefficient vector
spanning it, and the height is the norm of that vector. -/
theorem exists_prim_smul {f : MvPolynomial (Fin (n + 1)) ℚ} (hf : f ≠ 0)
    (hhom : f.IsHomogeneous d) :
    ∃ (a : Mon d n → ℤ) (c : ℚ), IsPrim a ∧ c ≠ 0 ∧ formOf d n a = c • f ∧
      HassePrincipleRandomFano.height f = eNorm a :=
  ⟨primVec (d := d) f, (clearance f : ℚ) / (clearGcd f : ℚ), IsPrim_primVec f hf hhom,
    div_ne_zero (by exact_mod_cast clearance_ne_zero hf)
      (by exact_mod_cast clearGcd_ne_zero hf),
    formOf_primVec f hf hhom, height_primVec f hf hhom⟩

/-! ## The bridge to projective space -/

theorem toV_surjective (d n : ℕ) (V : HassePrincipleRandomFano.𝕍 d n) :
    ∃ a : Mon d n → ℤ, IsPrim a ∧ toV a = V := by
  have hf : V.rep.1 ≠ 0 := by
    intro h0
    exact V.rep_nonzero (Subtype.ext h0)
  have hhom : V.rep.1.IsHomogeneous d := V.rep.2
  obtain ⟨a, c, hprim, hc, hform, -⟩ := exists_prim_smul (d := d) (f := V.rep.1) hf hhom
  refine ⟨a, hprim, ?_⟩
  have hne : toHom a ≠ 0 := toV_ne_zero_of_ne_zero a hprim.ne_zero
  have hsub : c • V.rep = toHom a := by
    refine Subtype.ext ?_
    show c • V.rep.1 = formOf d n a
    rw [hform]
  have hmk : Projectivization.mk ℚ (toHom a) hne = V := by
    rw [← Projectivization.mk_rep V]
    exact (Projectivization.mk_eq_mk_iff' ℚ (toHom a) V.rep hne V.rep_nonzero).2 ⟨c, hsub⟩
  rw [toV_of_ne_zero a hne]
  exact hmk

theorem height_rep (d n : ℕ) (a : Mon d n → ℤ) (ha : IsPrim a)
    (V : HassePrincipleRandomFano.𝕍 d n) (hV : toV a = V) :
    HassePrincipleRandomFano.height V.rep.1 = eNorm a := by
  have hne : toHom a ≠ 0 := toV_ne_zero_of_ne_zero a ha.ne_zero
  have hmk : Projectivization.mk ℚ (toHom a) hne
      = Projectivization.mk ℚ V.rep V.rep_nonzero :=
    (toV_of_ne_zero a hne).symm.trans (hV.trans (Projectivization.mk_rep V).symm)
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℚ (toHom a) V.rep hne V.rep_nonzero).1 hmk
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hne hc.symm
  have hcoe : V.rep.1 = c⁻¹ • formOf d n a := by
    have h := congrArg (fun x : homogeneousSubmodule (Fin (n + 1)) ℚ d =>
      (x : MvPolynomial (Fin (n + 1)) ℚ)) hc
    have h2 : c • V.rep.1 = formOf d n a := by simpa using h
    rw [← h2, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hf : V.rep.1 ≠ 0 := by
    intro h0
    exact V.rep_nonzero (Subtype.ext h0)
  have hhom : V.rep.1.IsHomogeneous d := V.rep.2
  obtain ⟨a', c', ha', hc', hform', hheight'⟩ :=
    exists_prim_smul (d := d) (f := V.rep.1) hf hhom
  have hspan : ∀ m : Mon d n, (a' m : ℚ) = (c' * c⁻¹) * (a m : ℚ) := by
    intro m
    have h := congrArg (fun p : MvPolynomial (Fin (n + 1)) ℚ =>
      p.coeff (Mon.toFinsupp m)) hform'
    rw [formOf_coeff, MvPolynomial.coeff_smul, hcoe, MvPolynomial.coeff_smul,
      formOf_coeff] at h
    rw [h, smul_eq_mul, smul_eq_mul]
    ring
  rcases BridgeAux.prim_eq_or_eq_neg ha' ha (c' * c⁻¹) hspan with h' | h'
  · rw [hheight', h']
  · rw [hheight', h', eNorm_neg]

theorem toV_eq_toV (d n : ℕ) (a b : Mon d n → ℤ) (ha : IsPrim a) (hb : IsPrim b) :
    toV a = toV b ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    have hA : toHom a ≠ 0 := toV_ne_zero_of_ne_zero a ha.ne_zero
    have hB : toHom b ≠ 0 := toV_ne_zero_of_ne_zero b hb.ne_zero
    rw [toV_of_ne_zero a hA, toV_of_ne_zero b hB] at h
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff' ℚ (toHom a) (toHom b) hA hB).1 h
    have hpoly : c • formOf d n b = formOf d n a := by
      have h1 := congrArg (fun x : homogeneousSubmodule (Fin (n + 1)) ℚ d =>
        (x : MvPolynomial (Fin (n + 1)) ℚ)) hc
      simpa using h1
    have hcoef : ∀ m : Mon d n, (a m : ℚ) = c * (b m : ℚ) := by
      intro m
      have h2 := congrArg (fun p : MvPolynomial (Fin (n + 1)) ℚ =>
        p.coeff (Mon.toFinsupp m)) hpoly
      rw [MvPolynomial.coeff_smul, formOf_coeff, formOf_coeff] at h2
      simpa [smul_eq_mul] using h2.symm
    exact BridgeAux.prim_eq_or_eq_neg ha hb c hcoef
  · rintro (h | h)
    · rw [h]
    · rw [h]
      have hB : toHom b ≠ 0 := toV_ne_zero_of_ne_zero b hb.ne_zero
      have hneg : toHom (-b) = -toHom b := by
        refine Subtype.ext ?_
        show formOf d n (-b) = -formOf d n b
        exact formOf_neg d n b
      have hne : toHom (-b) ≠ 0 := by rw [hneg]; exact neg_ne_zero.mpr hB
      have h1 : toV (-b) = Projectivization.mk ℚ (-toHom b) (neg_ne_zero.mpr hB) := by
        rw [toV_of_ne_zero (-b) hne]
        exact (Projectivization.mk_eq_mk_iff' ℚ (toHom (-b)) (-toHom b) hne
          (neg_ne_zero.mpr hB)).2 ⟨1, by rw [one_smul]; exact hneg.symm⟩
      have h2 : toV b = Projectivization.mk ℚ (toHom b) hB := toV_of_ne_zero b hB
      rw [h1, h2]
      exact (Projectivization.mk_eq_mk_iff' ℚ (-toHom b) (toHom b)
        (neg_ne_zero.mpr hB) hB).2 ⟨-1, by rw [neg_one_smul]⟩

end Work.HP
