import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic
import Submission.Work.BW.multiHom_assPrime
import Submission.Work.BW.rayPoly_eq
import Submission.Work.BW.rayHilb_finite
import Submission.Work.RB.graded_hilbert


/-! Auxiliary lemmas for `Submission.Work.BW.hset_zero_cosets`.

Content: the elementary group laws of `G = G_a × G_m^N` in the affine coordinates of
`DefsB`, the compatibility of `transl` with the group law, preservation of multihomogeneity
under the graded automorphisms `transl g`, and the routing of minimal primes through
associated primes.  -/

namespace Work.BW

section GroupLaws

variable {N : ℕ}

theorem hsc_gmul_assoc (a b c : Fin (N + 1) → ℂ) :
    gmul (gmul a b) c = gmul a (gmul b c) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [gmul, Fin.cons_zero, Fin.cons_succ, add_assoc]
  | succ j => simp [gmul, Fin.cons_zero, Fin.cons_succ, mul_assoc]

theorem hsc_gmul_comm (a b : Fin (N + 1) → ℂ) : gmul a b = gmul b a := by
  funext i
  induction i using Fin.cases with
  | zero => simp [gmul, Fin.cons_zero, Fin.cons_succ, add_comm]
  | succ j => simp [gmul, Fin.cons_zero, Fin.cons_succ, mul_comm]

theorem hsc_gmul_gone_left (b : Fin (N + 1) → ℂ) : gmul (gone N) b = b := by
  funext i
  induction i using Fin.cases with
  | zero => simp [gmul, gone, Fin.cons_zero, Fin.cons_succ]
  | succ j => simp [gmul, gone, Fin.cons_zero, Fin.cons_succ]

theorem hsc_gmul_gone_right (a : Fin (N + 1) → ℂ) : gmul a (gone N) = a := by
  funext i
  induction i using Fin.cases with
  | zero => simp [gmul, gone, Fin.cons_zero, Fin.cons_succ]
  | succ j => simp [gmul, gone, Fin.cons_zero, Fin.cons_succ]

theorem hsc_ginv_gone : ginv (gone N) = (gone N : Fin (N + 1) → ℂ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [ginv, gone, Fin.cons_zero, Fin.cons_succ]
  | succ j => simp [ginv, gone, Fin.cons_zero, Fin.cons_succ]

theorem hsc_inG_gone : InG (gone N : Fin (N + 1) → ℂ) := by
  intro i
  simp [gone, Fin.cons_succ]

theorem hsc_inG_gmul {a b : Fin (N + 1) → ℂ} (ha : InG a) (hb : InG b) : InG (gmul a b) := by
  intro i
  simp only [gmul, Fin.cons_succ]
  exact mul_ne_zero (ha i) (hb i)

theorem hsc_inG_ginv {a : Fin (N + 1) → ℂ} (ha : InG a) : InG (ginv a) := by
  intro i
  simp only [ginv, Fin.cons_succ]
  exact inv_ne_zero (ha i)

theorem hsc_gmul_ginv_left (a : Fin (N + 1) → ℂ) (ha : InG a) : gmul (ginv a) a = gone N := by
  funext i
  induction i using Fin.cases with
  | zero => simp [gmul, ginv, gone, Fin.cons_zero, Fin.cons_succ]
  | succ j =>
      simp only [gmul, ginv, gone, Fin.cons_zero, Fin.cons_succ]
      rw [inv_mul_cancel₀]
      exact ha j

theorem hsc_gmul_ginv_right (a : Fin (N + 1) → ℂ) (ha : InG a) : gmul a (ginv a) = gone N := by
  funext i
  induction i using Fin.cases with
  | zero => simp [gmul, ginv, gone, Fin.cons_zero, Fin.cons_succ]
  | succ j =>
      simp only [gmul, ginv, gone, Fin.cons_zero, Fin.cons_succ]
      rw [mul_inv_cancel₀]
      exact ha j

/-- `a · (a⁻¹ · b) = b` for `a ∈ G`. -/
theorem hsc_gmul_inv_cancel {a b : Fin (N + 1) → ℂ} (ha : InG a) :
    gmul a (gmul (ginv a) b) = b := by
  rw [← hsc_gmul_assoc, hsc_gmul_ginv_right a ha, hsc_gmul_gone_left]

end GroupLaws

section Transl

variable {N : ℕ}

theorem hsc_eval_transl (g : Fin (N + 1) → ℂ) (x : Fin (N + 1) × Fin 2 → ℂ) (F : MR N) :
    MvPolynomial.eval x (transl g F) = MvPolynomial.eval (coneAct g x) F :=
  (transl_basic g g).1 x F

theorem hsc_coneAct_conePt (g y : Fin (N + 1) → ℂ) :
    coneAct g (conePt N y) = conePt N (gmul g y) :=
  (transl_basic g g).2.1 y

theorem hsc_transl_transl (g h : Fin (N + 1) → ℂ) (F : MR N) :
    transl g (transl h F) = transl (gmul g h) F :=
  (transl_basic g h).2.2.1 F

theorem hsc_transl_homPiece (g : Fin (N + 1) → ℂ) (d : Fin (N + 1) →₀ ℕ) {F : MR N}
    (hF : F ∈ homPiece N d) : transl g F ∈ homPiece N d :=
  (transl_basic g g).2.2.2.1 d F hF

theorem hsc_transl_inv {g : Fin (N + 1) → ℂ} (hg : InG g) (F : MR N) :
    transl (ginv g) (transl g F) = F :=
  (transl_basic g g).2.2.2.2 hg F

theorem hsc_transl_gone (F : MR N) : transl (gone N) F = F := by
  have h1 : transl (gone N) (transl (gone N) F) = transl (gone N) F := by
    rw [hsc_transl_transl, hsc_gmul_gone_left]
  have h2 : transl (ginv (gone N)) (transl (gone N) F) = F :=
    hsc_transl_inv hsc_inG_gone F
  rw [hsc_ginv_gone] at h2
  rw [← h1]
  exact h2

/-- `transl (g⁻¹)` is a right inverse of `transl g` for `g ∈ G`. -/
theorem hsc_transl_right_inv {g : Fin (N + 1) → ℂ} (hg : InG g) (F : MR N) :
    transl g (transl (ginv g) F) = F := by
  rw [hsc_transl_transl, hsc_gmul_ginv_right g hg, hsc_transl_gone]

theorem hsc_transl_surj {g : Fin (N + 1) → ℂ} (hg : InG g) :
    Function.Surjective (transl g) := by
  intro F
  exact ⟨transl (ginv g) F, hsc_transl_right_inv hg F⟩

theorem hsc_transl_ginv_surj {g : Fin (N + 1) → ℂ} (hg : InG g) :
    Function.Surjective (transl (ginv g)) := by
  intro F
  exact ⟨transl g F, hsc_transl_inv hg F⟩

theorem hsc_transl_ginv_inj {g : Fin (N + 1) → ℂ} (hg : InG g) :
    Function.Injective (transl (ginv g)) := by
  intro F F' h
  have h1 : transl g (transl (ginv g) F) = transl g (transl (ginv g) F') := by rw [h]
  rwa [hsc_transl_right_inv hg F, hsc_transl_right_inv hg F'] at h1

/-- `transl (g⁻¹)` maps a prime to a prime (its kernel is trivial). -/
theorem hsc_map_ginv_isPrime {g : Fin (N + 1) → ℂ} (hg : InG g) {p : Ideal (MR N)}
    (hp : p.IsPrime) : (Ideal.map (transl (ginv g)) p).IsPrime := by
  haveI := hp
  refine Ideal.map_isPrime_of_surjective (f := (transl (ginv g) : MR N →+* MR N))
    (hsc_transl_ginv_surj hg) ?_
  intro x hx
  have hx' : transl (ginv g) x = 0 := by
    rw [← RingHom.coe_coe (transl (ginv g))]
    exact RingHom.mem_ker.mp hx
  have hx0 : x = 0 := by
    rw [← hsc_transl_right_inv hg x, hx', map_zero]
  rw [hx0]
  exact p.zero_mem

theorem hsc_map_transl_map_ginv {g : Fin (N + 1) → ℂ} (hg : InG g) (J : Ideal (MR N)) :
    Ideal.map (transl g) (Ideal.map (transl (ginv g)) J) = J := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Ideal.mem_map_iff_of_surjective (transl g) (hsc_transl_surj hg)] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Ideal.mem_map_iff_of_surjective (transl (ginv g)) (hsc_transl_ginv_surj hg)] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rwa [hsc_transl_right_inv hg]
  · intro x hx
    have heq : transl g (transl (ginv g) x) = x := hsc_transl_right_inv hg x
    rw [← heq]
    exact Ideal.mem_map_of_mem (transl g) (Ideal.mem_map_of_mem (transl (ginv g)) hx)

theorem hsc_map_gmul_transl {g h : Fin (N + 1) → ℂ} (hg : InG g) (hh : InG h)
    (J : Ideal (MR N)) :
    Ideal.map (transl (gmul g h)) J = Ideal.map (transl g) (Ideal.map (transl h) J) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Ideal.mem_map_iff_of_surjective (transl (gmul g h)) (hsc_transl_surj (hsc_inG_gmul hg hh))]
      at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← hsc_transl_transl g h y]
    exact Ideal.mem_map_of_mem (transl g) (Ideal.mem_map_of_mem (transl h) hy)
  · intro x hx
    rw [Ideal.mem_map_iff_of_surjective (transl g) (hsc_transl_surj hg)] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Ideal.mem_map_iff_of_surjective (transl h) (hsc_transl_surj hh)] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hsc_transl_transl g h z]
    exact Ideal.mem_map_of_mem (transl (gmul g h)) hz

end Transl

section ConeAct

variable {N : ℕ}

/-- The action of `G` on cone points is an action: applying `a` then `b` is applying `a·b`. -/
theorem hsc_coneAct_comp (a b : Fin (N + 1) → ℂ) (x : Fin (N + 1) × Fin 2 → ℂ) :
    coneAct b (coneAct a x) = coneAct (gmul a b) x := by
  funext v
  have h1 : MvPolynomial.eval (coneAct b (coneAct a x)) (MvPolynomial.X v)
      = MvPolynomial.eval (coneAct (gmul a b) x) (MvPolynomial.X v) := by
    rw [← hsc_eval_transl b (coneAct a x) (MvPolynomial.X v)]
    rw [← hsc_eval_transl a x (transl b (MvPolynomial.X v))]
    rw [hsc_transl_transl a b (MvPolynomial.X v)]
    exact hsc_eval_transl (gmul a b) x (MvPolynomial.X v)
  simpa using h1

theorem hsc_coneAct_gone (x : Fin (N + 1) × Fin 2 → ℂ) : coneAct (gone N) x = x := by
  funext v
  obtain ⟨i, j⟩ := v
  fin_cases j
  · simp [coneAct]
  · induction i using Fin.cases with
    | zero => simp [coneAct, gone, Fin.cons_zero, Fin.cons_succ]
    | succ k => simp [coneAct, gone, Fin.cons_zero, Fin.cons_succ]

theorem hsc_OnG_coneAct {g : Fin (N + 1) → ℂ} (hg : InG g) {x : Fin (N + 1) × Fin 2 → ℂ}
    (hx : OnG N x) : OnG N (coneAct g x) := by
  refine ⟨?_, ?_⟩
  · have h00 : coneAct g x (0, 0) = x (0, 0) := by simp [coneAct]
    rw [h00]; exact hx.1
  · intro i
    constructor
    · have hi0 : coneAct g x (i.succ, 0) = x (i.succ, 0) := by simp [coneAct]
      rw [hi0]; exact (hx.2 i).1
    · have hi1 : coneAct g x (i.succ, 1) = g (i.succ) * x (i.succ, 1) := by simp [coneAct]
      rw [hi1]
      exact mul_ne_zero (hg i) (hx.2 i).2

end ConeAct

section MultiHomMap

variable {N : ℕ}

/-- `transl g` preserves multihomogeneous ideals (it is a graded automorphism for `g ∈ G`). -/
theorem hsc_MultiHom_map_transl {p : Ideal (MR N)} (hp : MultiHom N p) {g : Fin (N + 1) → ℂ}
    (hg : InG g) : MultiHom N (Ideal.map (transl g) p) := by
  classical
  intro x hx d
  rw [Ideal.mem_map_iff_of_surjective (transl g) (hsc_transl_surj hg)] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨MvPolynomial.weightedHomogeneousComponent (mdeg N) d y, hp y hy d, ?_⟩
  -- the multihomogeneous components of `transl g y` are the images of those of `y`
  set s : Finset (Fin (N + 1) →₀ ℕ) :=
    (MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) (φ := y)).toFinset with hs
  have hdecomp : ∑ i ∈ s, MvPolynomial.weightedHomogeneousComponent (mdeg N) i y = y := by
    have h := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) y
    rw [finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) (φ := y))] at h
    exact h
  have hcomp : transl g y
      = ∑ i ∈ s, transl g (MvPolynomial.weightedHomogeneousComponent (mdeg N) i y) := by
    conv_lhs => rw [← hdecomp]
    exact map_sum (transl g) (fun i => MvPolynomial.weightedHomogeneousComponent (mdeg N) i y) s
  have h2 : MvPolynomial.weightedHomogeneousComponent (mdeg N) d (transl g y)
      = ∑ i ∈ s, MvPolynomial.weightedHomogeneousComponent (mdeg N) d
          (transl g (MvPolynomial.weightedHomogeneousComponent (mdeg N) i y)) := by
    conv_lhs => rw [hcomp]
    exact map_sum (MvPolynomial.weightedHomogeneousComponent (mdeg N) d)
      (fun i => transl g (MvPolynomial.weightedHomogeneousComponent (mdeg N) i y)) s
  rw [h2]
  have hterm : ∀ i ∈ s, MvPolynomial.weightedHomogeneousComponent (mdeg N) d
      (transl g (MvPolynomial.weightedHomogeneousComponent (mdeg N) i y))
      = if d = i then transl g (MvPolynomial.weightedHomogeneousComponent (mdeg N) i y)
        else 0 := by
    intro i _
    exact MvPolynomial.weightedHomogeneousComponent_of_mem
      (hsc_transl_homPiece g i (MvPolynomial.weightedHomogeneousComponent_mem (mdeg N) y i))
  rw [Finset.sum_congr rfl hterm]
  by_cases hd : d ∈ s
  · rw [Finset.sum_eq_single d]
    · simp [hd]
    · intro i hi hid
      rw [if_neg]
      intro hcontra
      exact hid hcontra.symm
    · intro hdnot
      exact absurd hd hdnot
  · have hsfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) (φ := y)
    have hzero : MvPolynomial.weightedHomogeneousComponent (mdeg N) d y = 0 := by
      by_contra hne
      exact hd (by rw [hs]; exact hsfin.mem_toFinset.mpr hne)
    rw [Finset.sum_eq_zero]
    · rw [hzero, map_zero]
    · intro i hi
      rw [if_neg]
      intro hcontra
      exact hd (hcontra ▸ hi)

end MultiHomMap

section MinimalPrimes

variable {N : ℕ}

theorem hsc_minimalPrimes_subset_ass (I : Ideal (MR N)) :
    I.minimalPrimes ⊆ associatedPrimes (MR N) (MR N ⧸ I) := by
  have hann : Module.annihilator (MR N) (MR N ⧸ I) = I := Ideal.annihilator_quotient
  intro p hp
  rw [← hann] at hp
  exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    (MR N) (MR N ⧸ I) hp

theorem hsc_multiHom_minimalPrimes {I : Ideal (MR N)} (hI : MultiHom N I) {p : Ideal (MR N)}
    (hp : p ∈ I.minimalPrimes) : MultiHom N p :=
  multiHom_assPrime I hI p (hsc_minimalPrimes_subset_ass I hp)

end MinimalPrimes

section Hset

variable {N q : ℕ}

theorem hsc_Hset_transl_mem {w : Fin q → Fin (N + 1) → ℂ} {𝔓 I : Ideal (MR N)}
    {g : Fin (N + 1) → ℂ} (hg : g ∈ Hset w 𝔓 I 0) {F : MR N} (hF : F ∈ I) :
    transl g F ∈ 𝔓 := by
  have h := hg.2 F hF (0 : Fin q → ℕ) (by simp)
  simpa [applyH] using h

end Hset

section MeetsGCoset

variable {N : ℕ}

theorem hsc_meetsG_mono {p q : Ideal (MR N)} (hpq : p ≤ q) (hq : MeetsG N q) : MeetsG N p := by
  obtain ⟨x, hx, hxle⟩ := hq
  exact ⟨x, hx, le_trans hpq hxle⟩

/-- Translation by an element of `G` sends the cone points of a prime meeting `G` again to
cone points over `G`. -/
theorem hsc_meetsG_map_ginv {g : Fin (N + 1) → ℂ} (hg : InG g) {𝔓 : Ideal (MR N)}
    (hG : MeetsG N 𝔓) : MeetsG N (Ideal.map (transl (ginv g)) 𝔓) := by
  obtain ⟨x, hxG, hxle⟩ := hG
  refine ⟨coneAct g x, hsc_OnG_coneAct hg hxG, ?_⟩
  intro F hF
  rw [Ideal.mem_map_iff_of_surjective (transl (ginv g)) (hsc_transl_ginv_surj hg)] at hF
  obtain ⟨H, hH, rfl⟩ := hF
  rw [ptIdeal, RingHom.mem_ker, hsc_eval_transl, hsc_coneAct_comp, hsc_gmul_ginv_right g hg,
    hsc_coneAct_gone]
  exact hxle hH

/-- If `f, g ∈ G` give the same prime `τ_{f⁻¹}𝔓 = τ_{g⁻¹}𝔓`, then `g` lies in the coset
`f · stabG 𝔓`. -/
theorem hsc_mem_coset {𝔓 : Ideal (MR N)} {f g : Fin (N + 1) → ℂ} (hf : InG f) (hg : InG g)
    (h : Ideal.map (transl (ginv f)) 𝔓 = Ideal.map (transl (ginv g)) 𝔓) :
    g ∈ gmul f '' stabG 𝔓 := by
  have hfinv : InG (ginv f) := hsc_inG_ginv hf
  refine ⟨gmul (ginv f) g, ?_, ?_⟩
  · refine ⟨hsc_inG_gmul hfinv hg, ?_⟩
    have hcomm : gmul (ginv f) g = gmul g (ginv f) := hsc_gmul_comm _ _
    rw [hcomm, hsc_map_gmul_transl hg hfinv 𝔓, h]
    exact hsc_map_transl_map_ginv hg 𝔓
  · rw [hsc_gmul_inv_cancel hf]

end MeetsGCoset


section RayPolyExistence

/-! ### Ray Hilbert polynomials from the multigraded Hilbert–Samuel theorem of `Work.RB`

The multigraded Hilbert–Samuel theorem `Work.RB.graded_hilbert` gives, for a multihomogeneous
ideal in a polynomial ring whose weights are basis vectors, eventual polynomiality of the Hilbert
function in the multidegree.  Specialised to the ray `d = t • D` (`D ≥ 1`) this is exactly the
statement that the ray Hilbert function is eventually polynomial. -/

variable {N : ℕ}

/-- Substituting `X i ↦ a i * x` commutes with evaluating a multivariate polynomial at `x`. -/
private lemma hsc_eval_eval₂Hom_ray (n : ℕ) (P : MvPolynomial (Fin n) ℚ) (a : Fin n → ℚ)
    (x : ℚ) :
    (MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X) P).eval x
      = P.eval (fun i => a i * x) := by
  let φ : MvPolynomial (Fin n) ℚ →+* ℚ := (Polynomial.evalRingHom x).comp
    (MvPolynomial.eval₂Hom Polynomial.C (fun i => Polynomial.C (a i) * Polynomial.X))
  let ψ : MvPolynomial (Fin n) ℚ →+* ℚ :=
    MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun i => a i * x)
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r; simp [φ, ψ]
    · intro i; simp [φ, ψ]
  exact congrFun (congrArg DFunLike.coe hφψ) P

/-- Existence of the ray Hilbert polynomial: for `D ≥ 1` and a multihomogeneous ideal `I` the
function `t ↦ dim (R/I)_{tD}` agrees with a polynomial in `t` for all large `t`. -/
theorem hsc_isRayPoly_of_multiHom (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : MultiHom N I) : ∃ P : Polynomial ℚ, IsRayPoly N D I P := by
  obtain ⟨P, M, hP⟩ := Work.RB.graded_hilbert (n := N + 1) (σ := Fin (N + 1) × Fin 2)
    (w := mdeg N) (fun v => ⟨v.1, rfl⟩) I (fun p hp d => hI p hp d)
  refine ⟨MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C ((D i : ℚ)) * Polynomial.X) P, ?_⟩
  rw [IsRayPoly]
  filter_upwards [Filter.eventually_ge_atTop M] with t ht
  have hdt : ∀ i : Fin (N + 1), M ≤ (t • D) i := by
    intro i
    rw [Finsupp.smul_apply, smul_eq_mul]
    calc M ≤ t := ht
      _ = t * 1 := (mul_one t).symm
      _ ≤ t * D i := Nat.mul_le_mul_left t (hD i)
  have h1 := hP (t • D) hdt
  have h2 : (fun i : Fin (N + 1) => (((t • D) i : ℕ) : ℚ)) =
      fun i => (D i : ℚ) * (t : ℚ) := by
    funext i
    rw [Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h2] at h1
  have h3 : ((rayHilb N D I t : ℕ) : ℚ) =
      ((Module.finrank ℂ (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) (t • D) ⧸
        Submodule.comap (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) (t • D)).subtype
          (I.restrictScalars ℂ)) : ℕ) : ℚ) := rfl
  rw [h3, h1, hsc_eval_eval₂Hom_ray]

/-- The monomial `∏ᵢ X_{i0}^{dᵢ}` has multidegree `d`: it lies in the piece `homPiece N d`. -/
private lemma hsc_prod_X_mem_homPiece {N : ℕ} (d : Fin (N + 1) →₀ ℕ) :
    (∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ (d i)) ∈ homPiece N d := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  have hprod : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ (d i)) : MR N)
      (∑ i : Fin (N + 1), (d i) • mdeg N (i, 0)) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod (R := ℂ) (σ := Fin (N + 1) × Fin 2)
      (ι := Fin (N + 1)) Finset.univ (fun i => MvPolynomial.X (i, 0) ^ (d i))
      (fun i => (d i) • mdeg N (i, 0))
    intro i _
    exact (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N) (i, 0)).pow (d i)
  convert hprod using 2
  ext j
  simp [mdeg, Finsupp.smul_single]

/-- On a point where `X_{i0} ≠ 0` for every `i`, the monomial `∏ᵢ X_{i0}^{aᵢ}` does not vanish. -/
private lemma hsc_eval_prod_X_ne_zero {N : ℕ} (x : Fin (N + 1) × Fin 2 → ℂ)
    (hx : ∀ i : Fin (N + 1), x (i, 0) ≠ 0) (a : Fin (N + 1) → ℕ) :
    MvPolynomial.eval x ((∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ (a i)) : MR N) ≠ 0 := by
  rw [map_prod]
  simp only [MvPolynomial.eval_X, MvPolynomial.eval_pow]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))

/-- An ideal meeting `G` has `rayHilb ≥ 1` in every degree `tD`: the monomial `∏ᵢ X_{i0}^{tDᵢ}`
lies in the piece `(R)_{tD}`, is nonzero at any point of `Z(I) ∩ G`, and therefore survives in
`(R/I)_{tD}`. -/
theorem hsc_rayHilb_pos_of_meetsG {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N))
    (hG : MeetsG N I) (t : ℕ) : 1 ≤ rayHilb N D I t := by
  obtain ⟨x, hx, hIx⟩ := hG
  have hx0 : ∀ i : Fin (N + 1), x (i, 0) ≠ 0 := by
    intro i
    induction i using Fin.cases with
    | zero => exact hx.1
    | succ j => exact (hx.2 j).1
  set m : MR N := ∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ ((t • D) i) with hm
  have hmmem : m ∈ homPiece N (t • D) := by
    rw [hm]; exact hsc_prod_X_mem_homPiece (t • D)
  have hmnot : m ∉ I := by
    intro hmem
    have hze : MvPolynomial.eval x m = 0 := by
      have h1 : m ∈ ptIdeal N x := hIx hmem
      rw [ptIdeal, RingHom.mem_ker] at h1
      exact h1
    have hne : MvPolynomial.eval x m ≠ 0 := by
      rw [hm]; exact hsc_eval_prod_X_ne_zero x hx0 (fun i => (t • D) i)
    exact hne hze
  have hfin : Module.Finite ℂ ↥(homPiece N (t • D)) := rayHilb_finite N (t • D)
  have hneq : (Submodule.Quotient.mk (p := Submodule.comap (homPiece N (t • D)).subtype
        (I.restrictScalars ℂ)) ⟨m, hmmem⟩ : ↥(homPiece N (t • D)) ⧸
        Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) ≠ 0 := by
    intro hzero
    rw [Submodule.Quotient.mk_eq_zero] at hzero
    exact hmnot (by simpa [Submodule.mem_comap] using hzero)
  have hnt : Nontrivial (↥(homPiece N (t • D)) ⧸
      Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) :=
    nontrivial_of_ne _ _ hneq
  have hpos : 0 < rayHilb N D I t := by
    rw [rayHilb]
    exact Module.finrank_pos
  omega


end RayPolyExistence
end Work.BW
