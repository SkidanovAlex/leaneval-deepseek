import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Data.Finsupp.Pointwise
import Submission.Commons.Analysis.InnerProductSpace.compl_norm_sq_eq
import Submission.Commons.Analysis.InnerProductSpace.erase_sum_sq_eq_if
import Submission.Commons.Analysis.MvPolynomial.eval_support_subset_two
import Submission.Commons.Analysis.MvPolynomial.coeff_odd_of_flip_invariant

noncomputable section
open scoped BigOperators RealInnerProductSpace
open MvPolynomial

namespace Commons.Algebra.MvPolynomial

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev e (n : ℕ) [NeZero n] (i : Fin n) : E n := EuclideanSpace.single i (1 : ℝ)

section Basic

variable {n : ℕ} [NeZero n]

private lemma single_inner_left (i : Fin n) (w : E n) : inner ℝ (EuclideanSpace.single i (1 : ℝ)) w = w i := by
  rw [EuclideanSpace.inner_single_left]; simp

private lemma norm_single_one (i : Fin n) : ‖(EuclideanSpace.single i (1 : ℝ) : E n)‖ = 1 := by simp

private lemma normSq_smul_add_smul_of_ne {z o : Fin n} (hzo : z ≠ o) (a b : ℝ) :
    ‖a • (EuclideanSpace.single z (1 : ℝ) : E n) + b • EuclideanSpace.single o (1 : ℝ)‖ ^ 2 =
      a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  have h1 : ‖a • (EuclideanSpace.single z (1 : ℝ) : E n)‖ ^ 2 = a ^ 2 := by simp [norm_smul]
  have h2 : ‖b • (EuclideanSpace.single o (1 : ℝ) : E n)‖ ^ 2 = b ^ 2 := by simp [norm_smul]
  have h3 : inner ℝ (a • (EuclideanSpace.single z (1 : ℝ) : E n))
      (b • EuclideanSpace.single o (1 : ℝ)) = 0 := by
    rw [inner_smul_left, inner_smul_right]
    rw [single_inner_left]
    simp [hzo]
  rw [h1, h2, h3]; ring

private lemma normSq_smul_add_of_ortho {z : Fin n} (w : E n) (a : ℝ)
    (horth : inner ℝ (EuclideanSpace.single z (1 : ℝ) : E n) w = 0) :
    ‖a • (EuclideanSpace.single z (1 : ℝ) : E n) + w‖ ^ 2 =
      a ^ 2 + ‖w‖ ^ 2 := by
  rw [norm_add_sq_real]
  have h1 : ‖a • (EuclideanSpace.single z (1 : ℝ) : E n)‖ ^ 2 = a ^ 2 := by simp [norm_smul]
  have h3 : inner ℝ (a • (EuclideanSpace.single z (1 : ℝ) : E n)) w = 0 := by
    rw [inner_smul_left]
    simp [horth]
  rw [h1, h3]; ring

/-- There is an isometry fixing coordinate `z` that maps the "profile point"
`(x z)•e_z + ‖x - (x z)•e_z‖ • e_o` back onto `x` (and fixes `e_z`). -/
private lemma exists_isometry_axis {z o : Fin n} (hzo : z ≠ o) (x : E n) :
    ∃ L : E n ≃ₗᵢ[ℝ] E n,
      L ((x z) • (EuclideanSpace.single z (1 : ℝ) : E n) +
          ‖x - (x z) • (EuclideanSpace.single z (1 : ℝ) : E n)‖ •
            EuclideanSpace.single o (1 : ℝ)) = x ∧
      L (EuclideanSpace.single z (1 : ℝ)) = EuclideanSpace.single z (1 : ℝ) := by
  let ez : E n := EuclideanSpace.single z (1 : ℝ)
  let eo : E n := EuclideanSpace.single o (1 : ℝ)
  let x0 : ℝ := x z
  let w : E n := x - x0 • ez
  let ρ : ℝ := ‖w‖
  let p : E n := x0 • ez + ρ • eo
  change ∃ L : E n ≃ₗᵢ[ℝ] E n, L p = x ∧ L ez = ez
  have hze : inner ℝ ez eo = 0 := by
    dsimp [ez, eo]
    rw [single_inner_left]
    simp [hzo]
  have horth_w : inner ℝ ez w = 0 := by
    dsimp [w, x0, ez]
    rw [inner_sub_right]
    have h1 : inner ℝ (EuclideanSpace.single z (1 : ℝ)) x = x z := single_inner_left z x
    have h2 : inner ℝ (EuclideanSpace.single z (1 : ℝ))
        (x z • (EuclideanSpace.single z (1 : ℝ) : E n)) = x z := by
      rw [inner_smul_right, single_inner_left]
      simp
    rw [h1, h2]
    ring
  have hsq_p : ‖p‖ ^ 2 = x0 ^ 2 + ρ ^ 2 := by
    dsimp [p]
    exact normSq_smul_add_smul_of_ne hzo x0 ρ
  have hdecomp : x = x0 • ez + w := by
    dsimp [w]
    abel
  have hsq_x : ‖x‖ ^ 2 = x0 ^ 2 + ρ ^ 2 := by
    rw [hdecomp]
    exact normSq_smul_add_of_ortho w x0 horth_w
  have hsq : ‖p‖ ^ 2 = ‖x‖ ^ 2 := by rw [hsq_p, hsq_x]
  have hs := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have hnorm : ‖p‖ = ‖x‖ := by
    rcases hs with h | h
    · exact h
    · have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
      have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
      nlinarith
  let R : E n ≃ₗᵢ[ℝ] E n := Submodule.reflection (ℝ ∙ (p - x))ᗮ
  refine ⟨R, ?_, ?_⟩
  · exact Submodule.reflection_sub hnorm
  · apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hpx : inner ℝ (p - x) ez = 0 := by
      have hpx' : p - x = ρ • eo - w := by
        dsimp [p]
        rw [hdecomp]
        abel
      rw [hpx']
      rw [inner_sub_left, inner_smul_left]
      have h1 : inner ℝ eo ez = 0 := by rw [real_inner_comm]; exact hze
      have h2 : inner ℝ w ez = 0 := by rw [real_inner_comm]; exact horth_w
      rw [h1, h2]
      simp
    rw [real_inner_comm]
    exact hpx

/-- The isometry that negates coordinate `o` (fixing all others), as a reflection. -/
private def coordFlip (o : Fin n) : E n ≃ₗᵢ[ℝ] E n :=
  Submodule.reflection (ℝ ∙ EuclideanSpace.single o (1 : ℝ))ᗮ

private lemma coordFlip_fix_of_ne {o z : Fin n} (hzo : z ≠ o) :
    coordFlip o (EuclideanSpace.single z (1 : ℝ)) = EuclideanSpace.single z (1 : ℝ) := by
  apply Submodule.reflection_mem_subspace_eq_self
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [single_inner_left]
  simp [hzo]

/-- Explicit decomposition of the coordinate-flip reflection. -/
private lemma coordFlip_eq (o : Fin n) (x : E n) :
    coordFlip o x = - (x o) • EuclideanSpace.single o (1 : ℝ) +
      (x - (x o) • EuclideanSpace.single o (1 : ℝ)) := by
  let K : Submodule ℝ (E n) := (ℝ ∙ EuclideanSpace.single o (1 : ℝ))ᗮ
  let z : E n := x - (x o) • EuclideanSpace.single o (1 : ℝ)
  have hx : x = (x o) • EuclideanSpace.single o (1 : ℝ) + z := by dsimp [z]; abel
  have hzK : z ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    dsimp [z]
    rw [inner_sub_right]
    have h1 : inner ℝ (EuclideanSpace.single o (1 : ℝ)) x = x o := single_inner_left o x
    have h2 : inner ℝ (EuclideanSpace.single o (1 : ℝ))
        ((x o) • EuclideanSpace.single o (1 : ℝ)) = x o := by
      rw [inner_smul_right, single_inner_left]
      simp
    rw [h1, h2]
    ring
  calc
    coordFlip o x = coordFlip o ((x o) • EuclideanSpace.single o (1 : ℝ) + z) := by
          conv_lhs => rw [hx]
    _ = (x o) • coordFlip o (EuclideanSpace.single o (1 : ℝ)) + coordFlip o z := by
          rw [map_add, map_smul]
    _ = (x o) • (- EuclideanSpace.single o (1 : ℝ)) + z := by
          have hf : coordFlip o (EuclideanSpace.single o (1 : ℝ)) = - EuclideanSpace.single o (1 : ℝ) := by
            rw [coordFlip]
            exact Submodule.reflection_orthogonalComplement_singleton_eq_neg
              (EuclideanSpace.single o (1 : ℝ))
          have hz : coordFlip o z = z := by
            rw [coordFlip]
            exact Submodule.reflection_mem_subspace_eq_self (K := K) hzK
          rw [hf, hz]
    _ = - (x o) • EuclideanSpace.single o (1 : ℝ) + z := by simp

private lemma coordFlip_neg (o : Fin n) (x : E n) : (coordFlip o x) o = - x o := by
  rw [coordFlip_eq]
  simp

private lemma coordFlip_coord (o : Fin n) (x : E n) (i : Fin n) : (coordFlip o x) i = if i = o then - x o else x i := by
  by_cases hi : i = o
  · subst i; simp [coordFlip_neg]
  · rw [coordFlip_eq]
    have hio : i ≠ o := hi
    simp [hio]

/-- Geometric flip invariance at the value level implies polynomial flip invariance. -/
private lemma bind_flip_inv_of_geom {o : Fin n} (P : MvPolynomial (Fin n) ℝ)
    (hIP : ∀ x : E n, MvPolynomial.eval (fun i => (coordFlip o x) i) P = MvPolynomial.eval (fun i => x i) P) :
    MvPolynomial.bind₁ (fun j : Fin n => if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) P = P := by
  apply MvPolynomial.funext
  intro y
  calc
    MvPolynomial.eval y (MvPolynomial.bind₁
        (fun j : Fin n => if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) P)
        = MvPolynomial.eval (fun j => MvPolynomial.eval y
            (if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j)) P := by
            change MvPolynomial.eval₂Hom (RingHom.id ℝ) y (MvPolynomial.bind₁
                (fun j : Fin n => if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) P)
              = MvPolynomial.eval₂Hom (RingHom.id ℝ)
                  (fun j => MvPolynomial.eval₂Hom (RingHom.id ℝ) y
                    (if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j)) P
            exact MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) y
              (fun j : Fin n => if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) P
    _ = MvPolynomial.eval (fun j => if j = o then - y j else y j) P := by
            apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
            funext j
            by_cases hj : j = o <;> simp [hj]
    _ = MvPolynomial.eval (fun i => (coordFlip o (WithLp.toLp 2 y)) i) P := by
            apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
            funext i
            rw [coordFlip_coord]
            by_cases hi : i = o <;> simp [hi]
    _ = MvPolynomial.eval y P := hIP (WithLp.toLp 2 y)

end Basic


section Profile

variable {n : ℕ} [NeZero n]

/-- Coordinates of the `q`-th monomial exponent `single 0 (k - 2*q) + single o (2*q)`. -/
private lemma exp_coord_zero {k : ℕ} (o : Fin n) (ho0 : o ≠ (0 : Fin n)) (q : ℕ) :
    (Finsupp.single (0 : Fin n) (k - 2 * q) + Finsupp.single o (2 * q)) (0 : Fin n) = k - 2 * q := by
  simp [ho0]

private lemma exp_coord_o {k : ℕ} (o : Fin n) (_ho0 : o ≠ (0 : Fin n)) (q : ℕ) :
    (Finsupp.single (0 : Fin n) (k - 2 * q) + Finsupp.single o (2 * q)) o = 2 * q := by
  by_cases h : (0 : Fin n) = o
  · exact False.elim (_ho0 h.symm)
  · simp [h]

private lemma exp_coord_other {k : ℕ} (o : Fin n) (ho0 : o ≠ (0 : Fin n)) {q : ℕ} {i : Fin n}
    (hi0 : i ≠ (0 : Fin n)) (hio : i ≠ o) :
    (Finsupp.single (0 : Fin n) (k - 2 * q) + Finsupp.single o (2 * q)) i = 0 := by
  simp [hi0, hio]

/-- The exponent map `q ↦ single 0 (k - 2*q) + single o (2*q)` is injective on `Fin (k/2+1)`. -/
private lemma exp_injective {k : ℕ} (o : Fin n) (ho0 : o ≠ (0 : Fin n)) :
    Set.InjOn (fun q : Fin (k / 2 + 1) =>
      Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
      (Finset.univ : Finset (Fin (k / 2 + 1))) := by
  intro a ha b hb hab
  have hcon := congrArg (fun m : Fin n →₀ ℕ => m o) hab
  have hca : (Finsupp.single (0 : Fin n) (k - 2 * (a : ℕ)) + Finsupp.single o (2 * (a : ℕ))) o
      = 2 * (a : ℕ) := exp_coord_o o ho0 (a : ℕ)
  have hcb : (Finsupp.single (0 : Fin n) (k - 2 * (b : ℕ)) + Finsupp.single o (2 * (b : ℕ))) o
      = 2 * (b : ℕ) := exp_coord_o o ho0 (b : ℕ)
  have hmul : 2 * (a : ℕ) = 2 * (b : ℕ) := by
    rw [hca, hcb] at hcon
    exact hcon
  apply Fin.ext
  omega

/-- Filtered support exponent `d` with `d 0 + d o = k` has the form of a `q`-monomial.
Every element of the filtered support set is in the image of the exponent map. -/
private lemma filtered_subset_image {k : ℕ} (o : Fin n) (ho0 : o ≠ (0 : Fin n))
    (P : MvPolynomial (Fin n) ℝ) (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (heven : ∀ d : Fin n →₀ ℕ, Odd (d o) → P.coeff d = 0) :
    (P.support.filter (fun d : Fin n →₀ ℕ => d (0 : Fin n) + d o = k)) ⊆
      (Finset.univ : Finset (Fin (k / 2 + 1))).image (fun q : Fin (k / 2 + 1) =>
        Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ))) := by
  intro d hd
  have hdmem : d ∈ P.support := (Finset.mem_filter.mp hd).1
  have hdab : d (0 : Fin n) + d o = k := (Finset.mem_filter.mp hd).2
  have hcoeff : P.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hdmem
  have hdw : Finsupp.weight (1 : Fin n → ℕ) d = k :=
    (MvPolynomial.mem_homogeneousSubmodule (n := k) P).mp hP (d := d) hcoeff
  -- even exponent in `o`
  have hEven : Even (d o) := by
    by_contra h
    have hodd : Odd (d o) := (Nat.even_or_odd (d o)).elim (fun hE => False.elim (h hE)) id
    exact hcoeff (heven d hodd)
  rcases hEven with ⟨m, hm⟩
  let q : ℕ := (d o) / 2
  have hq2 : d o = 2 * q := by
    dsimp [q]
    omega
  have hql : q ≤ k / 2 := by
    dsimp [q]
    have hle : d o ≤ k := by omega
    omega
  have hqmem : q < k / 2 + 1 := by omega
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨q, hqmem⟩, Finset.mem_univ _, ?_⟩
  ext i
  by_cases hi0 : i = (0 : Fin n)
  · subst i
    rw [exp_coord_zero o ho0 q]
    dsimp [q]
    omega
  · by_cases hio : i = o
    · subst i
      rw [exp_coord_o o ho0 q]
      exact hq2.symm
    · rw [exp_coord_other o ho0 hi0 hio]
      have hout := Commons.Analysis.MvPolynomial.eq_zero_outside_of_weight_eq_sum
        (a := (0 : Fin n)) (b := o) (show (0 : Fin n) ≠ o from fun h => ho0 h.symm) hdw hdab
      exact (hout i hi0 hio).symm

end Profile


section Main

variable {n : ℕ} [NeZero n]

/-- Profile evaluation of a homogeneous, coordinate-`o`-even polynomial along the
axis spanned by `e 0` and `e o`, expanded in the monomials `X0^(k-2q) X_o^(2q)`. -/
private lemma profile_expansion {k : ℕ} (o : Fin n) (ho0 : o ≠ (0 : Fin n))
    (P : MvPolynomial (Fin n) ℝ) (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (heven : ∀ d : Fin n →₀ ℕ, Odd (d o) → P.coeff d = 0)
    (t u : ℝ) :
    MvPolynomial.eval (fun i : Fin n => if i = (0 : Fin n) then t else if i = o then u else 0) P =
      ∑ q : Fin (k / 2 + 1),
        P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
          * t ^ (k - 2 * (q : ℕ)) * u ^ (2 * (q : ℕ)) := by
  classical
  let e : Fin (k / 2 + 1) → Fin n →₀ ℕ := fun q =>
    Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ))
  let f : (Fin n →₀ ℕ) → ℝ := fun d => P.coeff d * t ^ (d (0 : Fin n)) * u ^ (d o)
  let S : Finset (Fin n →₀ ℕ) :=
    P.support.filter (fun d : Fin n →₀ ℕ => d (0 : Fin n) + d o = k)
  let IM : Finset (Fin n →₀ ℕ) := (Finset.univ : Finset (Fin (k / 2 + 1))).image e
  have hfilter :
      MvPolynomial.eval (fun i : Fin n => if i = (0 : Fin n) then t else if i = o then u else 0) P =
        ∑ d ∈ S, P.coeff d * t ^ (d (0 : Fin n)) * u ^ (d o) := by
    have h := Commons.Analysis.MvPolynomial.eval_support_subset_two
      (a := (0 : Fin n)) (b := o) (show (0 : Fin n) ≠ o from fun h0 => ho0 h0.symm) P hP t u
    simpa [S] using h
  have hsub : S ⊆ IM := filtered_subset_image o ho0 P hP heven
  have hzero : ∀ d : Fin n →₀ ℕ, d ∈ IM → d ∉ S → f d = 0 := by
    intro d hdIM hdnotS
    rcases Finset.mem_image.mp hdIM with ⟨q, hqmem, hdq⟩
    have hcoeff0 : P.coeff d = 0 := by
      by_contra hc
      have hdw : Finsupp.weight (1 : Fin n → ℕ) d = k :=
        (MvPolynomial.mem_homogeneousSubmodule (n := k) P).mp hP (d := d) hc
      have hdsum : d (0 : Fin n) + d o = k := by
        rw [← hdq]
        have hqle : 2 * (q : ℕ) ≤ k := by
          have h : (q : ℕ) ≤ k / 2 := by omega
          omega
        rw [exp_coord_zero o ho0 (q : ℕ), exp_coord_o o ho0 (q : ℕ)]
        omega
      exact hdnotS (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hc, hdsum⟩)
    dsimp [f]
    rw [hcoeff0]
    simp
  have hsumS : (∑ d ∈ S, f d) = ∑ d ∈ IM, f d := by
    exact Finset.sum_subset hsub hzero
  have hinj : Set.InjOn e (Finset.univ : Finset (Fin (k / 2 + 1))) := by
    dsimp [e]
    exact exp_injective o ho0
  have hsumImg : (∑ d ∈ IM, f d) = ∑ q : Fin (k / 2 + 1), f (e q) := by
    simpa [IM] using (Finset.sum_image (s := (Finset.univ : Finset (Fin (k / 2 + 1))))
      (g := e) hinj : (∑ d ∈ (Finset.univ : Finset (Fin (k / 2 + 1))).image e, f d) =
        ∑ q ∈ (Finset.univ : Finset (Fin (k / 2 + 1))), f (e q))
  calc
    MvPolynomial.eval (fun i : Fin n => if i = (0 : Fin n) then t else if i = o then u else 0) P
        = ∑ d ∈ S, f d := by simpa [f] using hfilter
    _ = ∑ d ∈ IM, f d := hsumS
    _ = ∑ q : Fin (k / 2 + 1), f (e q) := hsumImg
    _ = ∑ q : Fin (k / 2 + 1),
        P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
          * t ^ (k - 2 * (q : ℕ)) * u ^ (2 * (q : ℕ)) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp [f, e, ho0]

end Main


section Value

variable {n : ℕ} [NeZero n]

/-- Polynomial flip invariance (negating coordinate `o`) follows from the geometric
isometry invariance hypothesis. -/
private lemma flip_inv_poly {o : Fin n} (ho0 : o ≠ (0 : Fin n))
    (P : MvPolynomial (Fin n) ℝ)
    (hIP : ∀ L : E n ≃ₗᵢ[ℝ] E n,
      L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
      ∀ x : E n, MvPolynomial.eval (fun i => (L x) i) P = MvPolynomial.eval (fun i => x i) P) :
    MvPolynomial.bind₁ (fun j : Fin n => if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) P = P := by
  apply bind_flip_inv_of_geom
  intro x
  exact hIP (coordFlip o)
    (coordFlip_fix_of_ne (show (0 : Fin n) ≠ o from fun h => ho0 h.symm)) x

/-- Value identity: an axis-invariant homogeneous polynomial evaluated at `x` equals
the sum over `q` of the coefficients of `X0^(k-2q) X_o^(2q)` times
`(x 0)^(k-2q) (‖complement‖²)^q`. -/
private lemma eval_eq_zonal_sum {k : ℕ} (o : Fin n) (ho0 : o ≠ (0 : Fin n))
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hIP : ∀ L : E n ≃ₗᵢ[ℝ] E n,
      L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
      ∀ x : E n, MvPolynomial.eval (fun i => (L x) i) P = MvPolynomial.eval (fun i => x i) P)
    (x : E n) :
    MvPolynomial.eval (fun i => x i) P =
      ∑ q : Fin (k / 2 + 1),
        P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
          * (x (0 : Fin n)) ^ (k - 2 * (q : ℕ)) *
            (‖x - (x (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)‖ ^ 2) ^ (q : ℕ) := by
  classical
  let e0v : E n := EuclideanSpace.single (0 : Fin n) (1 : ℝ)
  let x0 : ℝ := x (0 : Fin n)
  let w : E n := x - x0 • e0v
  let ρ : ℝ := ‖w‖
  let p : E n := x0 • e0v + ρ • EuclideanSpace.single o (1 : ℝ)
  have hflip : MvPolynomial.bind₁
      (fun j : Fin n => if j = o then -(MvPolynomial.X j : MvPolynomial (Fin n) ℝ) else MvPolynomial.X j) P = P :=
    flip_inv_poly ho0 P hIP
  have heven : ∀ d : Fin n →₀ ℕ, Odd (d o) → P.coeff d = 0 := fun d hodd =>
    Commons.Analysis.MvPolynomial.coeff_odd_of_flip_invariant o P d hodd hflip
  have hgeom : ∃ L : E n ≃ₗᵢ[ℝ] E n, L p = x ∧ L e0v = e0v := by
    dsimp [p, e0v]
    exact exists_isometry_axis (z := (0 : Fin n)) (o := o)
      (show (0 : Fin n) ≠ o from fun h => ho0 h.symm) x
  rcases hgeom with ⟨L, hLp, hLe0⟩
  have heval_L : MvPolynomial.eval (fun i => (L p) i) P = MvPolynomial.eval (fun i => p i) P :=
    hIP L hLe0 p
  have heval_x : MvPolynomial.eval (fun i => x i) P = MvPolynomial.eval (fun i => p i) P := by
    calc
      MvPolynomial.eval (fun i => x i) P = MvPolynomial.eval (fun i => (L p) i) P := by
        apply congrArg (fun f : Fin n → ℝ => MvPolynomial.eval f P)
        funext i
        rw [hLp]
      _ = MvPolynomial.eval (fun i => p i) P := heval_L
  have hpcoord : (fun i : Fin n => p i) =
      fun i : Fin n => if i = (0 : Fin n) then x0 else if i = o then ρ else 0 := by
    funext i
    by_cases hi0 : i = (0 : Fin n)
    · subst i
      dsimp [p, e0v]
      simp [show (0 : Fin n) ≠ o from fun h => ho0 h.symm]
    · by_cases hio : i = o
      · subst i
        dsimp [p, e0v]
        simp [hi0, ho0]
      · dsimp [p, e0v]
        simp [hi0, hio]
  have hprofile : MvPolynomial.eval (fun i : Fin n => p i) P =
      ∑ q : Fin (k / 2 + 1),
        P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
          * x0 ^ (k - 2 * (q : ℕ)) * ρ ^ (2 * (q : ℕ)) := by
    calc
      MvPolynomial.eval (fun i : Fin n => p i) P
          = MvPolynomial.eval (fun i : Fin n => if i = (0 : Fin n) then x0 else if i = o then ρ else 0) P := by
              rw [hpcoord]
      _ = ∑ q : Fin (k / 2 + 1),
          P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
            * x0 ^ (k - 2 * (q : ℕ)) * ρ ^ (2 * (q : ℕ)) := profile_expansion o ho0 P hP heven x0 ρ
  calc
    MvPolynomial.eval (fun i => x i) P = MvPolynomial.eval (fun i => p i) P := heval_x
    _ = ∑ q : Fin (k / 2 + 1),
        P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
          * x0 ^ (k - 2 * (q : ℕ)) * ρ ^ (2 * (q : ℕ)) := hprofile
    _ = ∑ q : Fin (k / 2 + 1),
        P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (q : ℕ)) + Finsupp.single o (2 * (q : ℕ)))
          * (x (0 : Fin n)) ^ (k - 2 * (q : ℕ)) *
            (‖x - (x (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)‖ ^ 2) ^ (q : ℕ) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [← pow_mul ρ 2 (q : ℕ)]

end Value


section Final

variable {n : ℕ} [NeZero n]

/-- Square of the norm of the coordinate-`0`-complement equals the sum of squares
of the remaining coordinates (subtype version). -/
private lemma normSq_compl_subtype (x : E n) :
    ‖x - (x (0 : Fin n)) • (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : E n)‖ ^ 2 =
      ∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (x (i : Fin n)) ^ 2 := by
  classical
  have h1 := Commons.Analysis.InnerProductSpace.compl_norm_sq_eq x
  have h2 := Commons.Analysis.InnerProductSpace.erase_sum_sq_eq_if x
  calc
    ‖x - (x (0 : Fin n)) • (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : E n)‖ ^ 2
        = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n), (x i) ^ 2 := by
            rw [h1]
            exact h2.symm
    _ = ∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (x (i : Fin n)) ^ 2 := by
            exact Finset.sum_subtype (s := (Finset.univ : Finset (Fin n)).erase (0 : Fin n))
              (h := by intro i; simp) (f := fun i => (x i) ^ 2)

theorem axisInv_homogeneous_structure
    {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hIP : ∀ L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      L (EuclideanSpace.single (0 : Fin n) (1 : ℝ)) = EuclideanSpace.single (0 : Fin n) (1 : ℝ) →
      ∀ x : EuclideanSpace ℝ (Fin n),
        MvPolynomial.eval (fun i : Fin n => (L x) i) P =
          MvPolynomial.eval (fun i : Fin n => x i) P) :
    ∃ c : Fin (k / 2 + 1) → ℝ,
      P = ∑ j : Fin (k / 2 + 1),
        (c j) • ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2 * (j : ℕ)) *
          ((∑ i : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ) ^ 2) ^ (j : ℕ))) := by
  classical
  let o : Fin n := ⟨1, by omega⟩
  have ho0 : o ≠ (0 : Fin n) := by
    subst o
    simp
  let c : Fin (k / 2 + 1) → ℝ := fun j =>
    P.coeff (Finsupp.single (0 : Fin n) (k - 2 * (j : ℕ)) + Finsupp.single o (2 * (j : ℕ)))
  let S : MvPolynomial (Fin n) ℝ :=
    ∑ i : {i : Fin n // i ≠ (0 : Fin n)},
      (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ) ^ 2
  let Q : MvPolynomial (Fin n) ℝ :=
    ∑ j : Fin (k / 2 + 1), (c j) • ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2 * (j : ℕ)) * S ^ (j : ℕ))
  have hcoord_toLp : ∀ y : Fin n → ℝ, (fun i : Fin n => ((WithLp.toLp 2 y) : E n) i) = y := by
    intro y
    funext i
    rfl
  have hQeval : ∀ y : Fin n → ℝ,
      MvPolynomial.eval y Q =
        ∑ j : Fin (k / 2 + 1), (c j) * (y (0 : Fin n)) ^ (k - 2 * (j : ℕ)) *
          ((∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (y (i : Fin n)) ^ 2) ^ (j : ℕ)) := by
    intro y
    dsimp [Q, S]
    simp
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hPeval : ∀ y : Fin n → ℝ,
      MvPolynomial.eval y P =
        ∑ j : Fin (k / 2 + 1), (c j) * (y (0 : Fin n)) ^ (k - 2 * (j : ℕ)) *
          ((∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (y (i : Fin n)) ^ 2) ^ (j : ℕ)) := by
    intro y
    have hv := eval_eq_zonal_sum (o := o) ho0 P hP hIP ((WithLp.toLp 2 y) : E n)
    have hnorm : ‖((WithLp.toLp 2 y) : E n) -
        (((WithLp.toLp 2 y) : E n) (0 : Fin n)) •
          (EuclideanSpace.single (0 : Fin n) (1 : ℝ) : E n)‖ ^ 2 =
        ∑ i : {i : Fin n // i ≠ (0 : Fin n)}, (y (i : Fin n)) ^ 2 := by
      rw [normSq_compl_subtype]
    -- target RHS is the same as hv's RHS, with the norm-square replaced and c unfolded
    simpa [c, hnorm, hcoord_toLp] using hv
  refine ⟨c, ?_⟩
  apply MvPolynomial.funext
  intro y
  rw [hPeval y, hQeval y]

end Final

end Commons.Algebra.MvPolynomial