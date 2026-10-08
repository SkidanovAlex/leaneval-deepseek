import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

open LinearMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-! ## Preliminary material

We prove the "commutant dimension bound" for a nilpotent endomorphism, in the form
`finrank V ^ 2 ≤ r * finrank (commutant N)` when `N ^ r = 0`.

The proof goes by strong induction on `r`.  The key geometric input is the short exact
sequence `0 → ker N → V → N.range → 0` which shows that every endomorphism commuting with `N`
restricts to an endomorphism of `N.range` commuting with `N.rangeRestr N`, and that this
restriction map is surjective, with kernel of dimension `(finrank (ker N)) ^ 2`. -/

/-- `N.range` is stable under `N`. -/
lemma range_le_comap_self (N : Module.End K V) : N.range ≤ (N.range).comap N := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨N y, rfl⟩

/-- `N` restricted to its range `N.range`. -/
noncomputable def rangeRestr (N : Module.End K V) : Module.End K N.range :=
  N.restrict (range_le_comap_self N)

/-- A linear section of `N : V → N.range`. -/
lemma exists_section_range (N : Module.End K V) :
    ∃ σ : N.range →ₗ[K] V, N.comp σ = N.range.subtype := by
  have h : N.rangeRestrict.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro u
    obtain ⟨v, hv⟩ := u.property
    exact ⟨v, Subtype.ext hv⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective N.rangeRestrict h
  refine ⟨g, ?_⟩
  ext v
  have := congr_fun (congr_arg DFunLike.coe hg) v
  simp only [LinearMap.id_coe] at this
  have h2 : N (g v) = (v : V) := congrArg Subtype.val this
  simpa using h2

/-- A linear retraction `V → N.range` of the inclusion. -/
lemma exists_retraction_range (N : Module.End K V) :
    ∃ P : V →ₗ[K] N.range, P.comp N.range.subtype = LinearMap.id := by
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective N.range.subtype (by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective)
  exact ⟨P, hP⟩

/-- An element of the commutant of `N` maps `N.range` into itself. -/
lemma map_mem_range_of_mem_commutant (N : Module.End K V) {M : Module.End K V}
    (hM : M ∈ commutant N) {x : V} (hx : x ∈ N.range) : M x ∈ N.range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨M y, ?_⟩
  have h := congr_fun (congr_arg DFunLike.coe (mem_commutant_iff.mp hM)) y
  simpa [Module.End.mul_apply] using h

/-- The candidate lift of an endomorphism of `N.range` to `V`, built from a linear section `σ`
of `N` and a linear retraction `P` of the inclusion `N.range → V`. -/
noncomputable def lift (N : Module.End K V) (σ : N.range →ₗ[K] V) (P : V →ₗ[K] N.range)
    (Mbar : Module.End K N.range) : Module.End K V :=
  σ.comp (Mbar.comp N.rangeRestrict)
    + (N.range.subtype.comp Mbar - σ.comp (Mbar.comp (rangeRestr N))).comp P

/-- The lift restricts to `Mbar` on `N.range`. -/
lemma lift_restrict (N : Module.End K V) (σ : N.range →ₗ[K] V) (P : V →ₗ[K] N.range)
    (hP : P.comp N.range.subtype = LinearMap.id) (Mbar : Module.End K N.range) :
    (lift N σ P Mbar).comp N.range.subtype = N.range.subtype.comp Mbar := by
  ext u
  have hPid : P (N.range.subtype u) = u := by
    have := congr_fun (congr_arg DFunLike.coe hP) u
    simpa using this
  simp only [lift, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply]
  rw [show N.rangeRestrict (N.range.subtype u) = rangeRestr N u from Subtype.ext rfl, hPid]
  abel

/-- The lift of an element of the commutant of `N.rangeRestr N` lies in the commutant of `N`. -/
lemma lift_mem_commutant (N : Module.End K V) (σ : N.range →ₗ[K] V)
    (hσ : N.comp σ = N.range.subtype) (P : V →ₗ[K] N.range)
    (hP : P.comp N.range.subtype = LinearMap.id) {Mbar : Module.End K N.range}
    (hMbar : Mbar ∈ commutant (rangeRestr N)) :
    lift N σ P Mbar ∈ commutant N := by
  rw [mem_commutant_iff] at hMbar ⊢
  have hPid : ∀ u : N.range, P (N.range.subtype u) = u := by
    intro u; have := congr_fun (congr_arg DFunLike.coe hP) u; simpa using this
  have hσid : ∀ u : N.range, N (σ u) = (u : V) := by
    intro u; have := congr_fun (congr_arg DFunLike.coe hσ) u; simpa using this
  have hMbv : ∀ x : N.range, (rangeRestr N) (Mbar x) = Mbar ((rangeRestr N) x) := by
    intro x
    have := congr_fun (congr_arg DFunLike.coe hMbar) x
    simpa [Module.End.mul_apply] using this
  have hRci : ∀ w : N.range, N (N.range.subtype w) = ((rangeRestr N) w : V) := fun w => rfl
  have key : ∀ v : V, (lift N σ P Mbar) (N v) = (Mbar (N.rangeRestrict v) : V) := by
    intro v
    simp only [lift, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply]
    rw [show N.rangeRestrict (N v) = rangeRestr N (N.rangeRestrict v) from Subtype.ext rfl]
    rw [show P (N v) = N.rangeRestrict v from by
      rw [show N v = N.range.subtype (N.rangeRestrict v) from rfl, hPid]]
    abel
  have key2 : ∀ v : V, N ((lift N σ P Mbar) v) = (Mbar (N.rangeRestrict v) : V) := by
    intro v
    simp only [lift, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      map_add, map_sub]
    rw [hσid (Mbar (N.rangeRestrict v))]
    rw [hRci (Mbar (P v)), hMbv (P v), hσid (Mbar (rangeRestr N (P v)))]
    abel
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply, key v, key2 v]

/-- Restriction of an endomorphism of `V` to `N.range`, realised using the retraction `P`. -/
noncomputable def resHom (N : Module.End K V) (P : V →ₗ[K] N.range) :
    Module.End K V →ₗ[K] Module.End K N.range where
  toFun M := P.comp (M.comp N.range.subtype)
  map_add' M M' := by
    ext u; simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c M := by
    ext u; simp [LinearMap.smul_comp, LinearMap.comp_smul]

/-- The restriction of elements of the commutant of `N` to `N.range`. -/
noncomputable def Phi (N : Module.End K V) (P : V →ₗ[K] N.range) :
    commutant N →ₗ[K] Module.End K N.range :=
  (resHom N P).comp (commutant N).subtype

lemma Phi_apply (N : Module.End K V) (P : V →ₗ[K] N.range) (M : commutant N) :
    Phi N P M = P.comp ((M : Module.End K V).comp N.range.subtype) := rfl

/-- `Phi` lands in the commutant of `N.rangeRestr N`. -/
lemma Phi_mem (N : Module.End K V) (P : V →ₗ[K] N.range)
    (hP : P.comp N.range.subtype = LinearMap.id) (M : commutant N) :
    Phi N P M ∈ commutant (rangeRestr N) := by
  have hM : (M : Module.End K V) ∈ commutant N := M.property
  have hMU : ∀ x ∈ N.range, (M : Module.End K V) x ∈ N.range :=
    fun x hx => map_mem_range_of_mem_commutant N hM hx
  have hPid : ∀ u : N.range, P (N.range.subtype u) = u := by
    intro u; have := congr_fun (congr_arg DFunLike.coe hP) u; simpa using this
  have hrestrict : Phi N P M = (M : Module.End K V).restrict hMU := by
    ext u
    rw [show Phi N P M = P.comp ((M : Module.End K V).comp N.range.subtype) from rfl]
    simp only [LinearMap.comp_apply, LinearMap.restrict_apply, Subtype.coe_mk]
    rw [show (M : Module.End K V) (N.range.subtype u)
          = N.range.subtype ⟨(M : Module.End K V) (N.range.subtype u), hMU ↑u u.property⟩
          from rfl]
    simp only [hPid]
    rfl
  rw [hrestrict, mem_commutant_iff]
  have hMm := (mem_commutant_iff).mp hM
  ext u
  simp only [Module.End.mul_apply, LinearMap.restrict_apply, Subtype.coe_mk, rangeRestr]
  have h := congr_fun (congr_arg DFunLike.coe hMm) (u : V)
  simpa [Module.End.mul_apply] using h

/-- Every element of the commutant of `N.rangeRestr N` is the restriction of an element of the
commutant of `N`. -/
lemma Phi_surj (N : Module.End K V) (σ : N.range →ₗ[K] V) (hσ : N.comp σ = N.range.subtype)
    (P : V →ₗ[K] N.range) (hP : P.comp N.range.subtype = LinearMap.id)
    (Mbar : commutant (rangeRestr N)) :
    ∃ M : commutant N, Phi N P M = (Mbar : Module.End K N.range) := by
  refine ⟨⟨lift N σ P (Mbar : Module.End K N.range),
    lift_mem_commutant N σ hσ P hP Mbar.property⟩, ?_⟩
  have h1 : (lift N σ P (Mbar : Module.End K N.range)).comp N.range.subtype
      = N.range.subtype.comp (Mbar : Module.End K N.range) :=
    lift_restrict N σ P hP (Mbar : Module.End K N.range)
  show P.comp ((lift N σ P (Mbar : Module.End K N.range)).comp N.range.subtype)
      = (Mbar : Module.End K N.range)
  rw [h1, ← LinearMap.comp_assoc, hP, LinearMap.id_comp]

/-- The range of `Phi` is exactly the commutant of `N.rangeRestr N`. -/
lemma Phi_range (N : Module.End K V) (σ : N.range →ₗ[K] V) (hσ : N.comp σ = N.range.subtype)
    (P : V →ₗ[K] N.range) (hP : P.comp N.range.subtype = LinearMap.id) :
    (Phi N P).range = commutant (rangeRestr N) := by
  ext X
  constructor
  · intro hX
    obtain ⟨M, rfl⟩ := LinearMap.mem_range.mp hX
    exact Phi_mem N P hP M
  · intro hX
    obtain ⟨M, hM⟩ := Phi_surj N σ hσ P hP ⟨X, hX⟩
    exact LinearMap.mem_range.mpr ⟨M, hM⟩

/-! ### The kernel of the restriction map -/

/-- The map `(V ⧸ N.range →ₗ N.ker) →ₗ End K V`, `g ↦ (v ↦ g (v mod N.range))`. -/
noncomputable def theta0 (N : Module.End K V) :
    (V ⧸ N.range →ₗ[K] N.ker) →ₗ[K] Module.End K V where
  toFun g := N.ker.subtype.comp (g.comp N.range.mkQ)
  map_add' g g' := by ext v; simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c g := by ext v; simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma theta0_apply (N : Module.End K V) (g : V ⧸ N.range →ₗ[K] N.ker) (v : V) :
    (theta0 N g) v = N.ker.subtype (g (N.range.mkQ v)) := rfl

/-- `theta0` lands in the commutant of `N`. -/
lemma theta0_mem_commutant (N : Module.End K V) (g : V ⧸ N.range →ₗ[K] N.ker) :
    theta0 N g ∈ commutant N := by
  rw [mem_commutant_iff]
  ext v
  have h1 : (theta0 N g) (N v) = 0 := by
    rw [theta0_apply]
    rw [show N.range.mkQ (N v) = 0 from by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨v, rfl⟩]
    simp
  have h2 : N ((theta0 N g) v) = 0 := by
    rw [theta0_apply]
    exact LinearMap.mem_ker.mp (g (N.range.mkQ v)).property
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2]

/-- `theta0` with codomain the commutant of `N`. -/
noncomputable def theta (N : Module.End K V) :
    (V ⧸ N.range →ₗ[K] N.ker) →ₗ[K] commutant N :=
  LinearMap.codRestrict (commutant N) (theta0 N) (fun g => theta0_mem_commutant N g)

lemma theta0_comp_subtype (N : Module.End K V) (g : V ⧸ N.range →ₗ[K] N.ker) :
    (theta0 N g).comp N.range.subtype = 0 := by
  ext u
  rw [LinearMap.comp_apply, theta0_apply, LinearMap.zero_apply]
  rw [show N.range.mkQ (N.range.subtype u) = 0 from by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact u.property]
  simp

/-- `theta` lands in the kernel of `Phi`. -/
lemma theta_mem_ker (N : Module.End K V) (P : V →ₗ[K] N.range)
    (hP : P.comp N.range.subtype = LinearMap.id) (g : V ⧸ N.range →ₗ[K] N.ker) :
    theta N g ∈ (Phi N P).ker := by
  rw [LinearMap.mem_ker]
  show P.comp (((theta N g : commutant N) : Module.End K V).comp N.range.subtype) = 0
  rw [show ((theta N g : commutant N) : Module.End K V) = theta0 N g from rfl,
    theta0_comp_subtype, LinearMap.comp_zero]

/-- `theta` as a map into the kernel of `Phi`. -/
noncomputable def thetaK (N : Module.End K V) (P : V →ₗ[K] N.range)
    (hP : P.comp N.range.subtype = LinearMap.id) :
    (V ⧸ N.range →ₗ[K] N.ker) →ₗ[K] (Phi N P).ker :=
  LinearMap.codRestrict ((Phi N P).ker) (theta N) (fun g => theta_mem_ker N P hP g)

lemma theta_injective (N : Module.End K V) : Function.Injective (theta N) := by
  intro g g' h
  have hco : theta0 N g = theta0 N g' := by
    have := congrArg Subtype.val h
    simpa only [theta, LinearMap.codRestrict_apply] using this
  apply LinearMap.ext
  intro w
  obtain ⟨v, hv⟩ := Submodule.mkQ_surjective N.range w
  have h2 := congr_fun (congr_arg DFunLike.coe hco) v
  rw [theta0_apply, theta0_apply] at h2
  rw [← hv]
  exact Subtype.ext h2

lemma thetaK_injective (N : Module.End K V) (P : V →ₗ[K] N.range)
    (hP : P.comp N.range.subtype = LinearMap.id) : Function.Injective (thetaK N P hP) := by
  intro a b hab
  exact theta_injective N (by
    have := congrArg Subtype.val hab
    simpa only [thetaK, LinearMap.codRestrict_apply] using this)

/-- The kernel of `Phi` has dimension at least `(finrank (ker N))²`. -/
lemma finrank_ker_Phi_ge (N : Module.End K V) [FiniteDimensional K V] (P : V →ₗ[K] N.range)
    (hP : P.comp N.range.subtype = LinearMap.id) :
    (Module.finrank K N.ker) ^ 2 ≤ Module.finrank K (Phi N P).ker := by
  have h1 : Module.finrank K (V ⧸ N.range →ₗ[K] N.ker) ≤ Module.finrank K (Phi N P).ker :=
    LinearMap.finrank_le_finrank_of_injective (thetaK_injective N P hP)
  have h2 : Module.finrank K (V ⧸ N.range →ₗ[K] N.ker)
      = Module.finrank K (V ⧸ N.range) * Module.finrank K N.ker :=
    Module.finrank_linearMap K K (V ⧸ N.range) N.ker
  have h3 : Module.finrank K (V ⧸ N.range) + Module.finrank K N.range = Module.finrank K V :=
    Submodule.finrank_quotient_add_finrank N.range
  have h4 : Module.finrank K N.range + Module.finrank K N.ker = Module.finrank K V :=
    LinearMap.finrank_range_add_finrank_ker N
  have h5 : Module.finrank K (V ⧸ N.range) = Module.finrank K N.ker := by omega
  rw [h2, h5] at h1
  simpa [pow_two] using h1

/-- The recursion: the dimension of the commutant of `N` is at least the dimension of the
commutant of `N.rangeRestr N` plus the square of the dimension of `N.ker`. -/
theorem finrank_commutant_ge (N : Module.End K V) [FiniteDimensional K V] :
    Module.finrank K (commutant (rangeRestr N)) + (Module.finrank K N.ker) ^ 2
      ≤ Module.finrank K (commutant N) := by
  obtain ⟨σ, hσ⟩ := exists_section_range N
  obtain ⟨P, hP⟩ := exists_retraction_range N
  have hrn := LinearMap.finrank_range_add_finrank_ker (Phi N P)
  rw [Phi_range N σ hσ P hP] at hrn
  have hk := finrank_ker_Phi_ge N P hP
  omega

/-- `(rangeRestr N) ^ m = 0` whenever `N ^ (m+1) = 0`. -/
lemma rangeRestr_pow_eq_zero (N : Module.End K V) {m : ℕ} (h : N ^ (m + 1) = 0) :
    (rangeRestr N) ^ m = 0 := by
  rw [rangeRestr, Module.End.pow_restrict]
  ext u
  simp only [LinearMap.restrict_apply, LinearMap.zero_apply, Subtype.coe_mk]
  obtain ⟨y, hy⟩ := u.property
  rw [show (u : V) = N y from hy.symm, ← Module.End.mul_apply, ← pow_succ, h]
  simp

/-- The dimension of the commutant of `0` is `(finrank V)²`. -/
lemma finrank_commutant_zero (N : Module.End K V) [FiniteDimensional K V] (hN0 : N = 0) :
    Module.finrank K (commutant N) = (Module.finrank K V) ^ 2 := by
  have hcomm : commutant N = ⊤ := by
    rw [hN0]; ext Y; rw [mem_commutant_iff]; simp
  rw [hcomm, (Submodule.topEquiv (R := K) (M := Module.End K V)).finrank_eq]
  change Module.finrank K (V →ₗ[K] V) = Module.finrank K V ^ 2
  rw [Module.finrank_linearMap K K V V, pow_two]

/-- Arithmetic core of the induction. -/
lemma arith_helper (k d b C E : ℕ) (h1 : d ^ 2 ≤ (k + 1) * E) (h2 : E + b ^ 2 ≤ C) :
    (d + b) ^ 2 ≤ (k + 2) * C := by
  have amgm : 2 * d * ((k + 1) * b) ≤ d ^ 2 + ((k + 1) * b) ^ 2 := by
    nlinarith [sq_nonneg ((d : ℤ) - ((k + 1) * b : ℤ))]
  have hk : 0 < k + 1 := by omega
  suffices h : (k + 1) * (d + b) ^ 2 ≤ (k + 1) * ((k + 2) * C) by
    exact Nat.le_of_mul_le_mul_left h hk
  calc (k + 1) * (d + b) ^ 2 ≤ (k + 2) * d ^ 2 + (k + 1) * (k + 2) * b ^ 2 := by
        nlinarith [amgm]
    _ ≤ (k + 2) * ((k + 1) * E) + (k + 1) * (k + 2) * b ^ 2 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _
    _ = (k + 1) * ((k + 2) * E) + (k + 1) * (k + 2) * b ^ 2 := by ring
    _ = (k + 1) * ((k + 2) * (E + b ^ 2)) := by ring
    _ ≤ (k + 1) * ((k + 2) * C) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)

section Induction

universe u

/-- Auxiliary form of the bound, proved by strong induction on `r`. -/
theorem sq_finrank_le_mul_finrank_commutant_aux (r : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (N : Module.End K V), N ^ r = 0 →
      Module.finrank K V ^ 2 ≤ r * Module.finrank K (commutant N) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro V _ _ _ N hN
    rcases r with _ | k
    · -- r = 0
      have h1 : (1 : Module.End K V) = 0 := by simpa using hN
      have hsub : Subsingleton V := by
        have ha : ∀ a : V, a = 0 := fun a => by
          have h : (1 : Module.End K V) a = (0 : Module.End K V) a := by rw [h1]
          simpa using h
        exact ⟨fun a b => by rw [ha a, ha b]⟩
      haveI := hsub
      have hf : Module.finrank K V = 0 :=
        Module.finrank_zero_of_subsingleton (R := K) (M := V)
      rw [hf]; simp
    · rcases k with _ | k
      · -- r = 1
        have hN0 : N = 0 := by simpa using hN
        rw [finrank_commutant_zero N hN0]
        simp
      · -- r = k + 2
        by_cases hN0 : N = 0
        · rw [finrank_commutant_zero N hN0]
          have hr : 1 ≤ k + 2 := by omega
          calc (Module.finrank K V) ^ 2 = 1 * (Module.finrank K V) ^ 2 := by ring
            _ ≤ (k + 2) * (Module.finrank K V) ^ 2 := Nat.mul_le_mul_right _ hr
        · have hbar : (rangeRestr N) ^ (k + 1) = 0 := rangeRestr_pow_eq_zero N hN
          have hIH := ih (k + 1) (by omega) (N.range) (rangeRestr N) hbar
          have hrec := finrank_commutant_ge N
          have hrn := LinearMap.finrank_range_add_finrank_ker N
          rw [← hrn]
          exact arith_helper k _ _ _ _ hIH hrec

end Induction

/-! ## The target statement -/

/-- Step 4e of the GL-core proof of Hall--Higman B: if the endomorphism `N` satisfies `N ^ r = 0`
then the square of the dimension of `V` is at most `r` times the dimension of the commutant of `N`. -/
lemma sq_finrank_le_mul_finrank_commutant {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (N : Module.End K V) {r : ℕ} (hN : N ^ r = 0) :
    Module.finrank K V ^ 2 ≤ r * Module.finrank K (Work.HallHigman.commutant N) :=
  sq_finrank_le_mul_finrank_commutant_aux r V N hN

end Work.HallHigman.GLCore

