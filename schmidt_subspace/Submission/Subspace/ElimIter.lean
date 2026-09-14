import Mathlib
import Submission.Commons.Algebra.MvPolynomial.pderivIter_properties
import Submission.Commons.Algebra.MvPolynomial.pderivIter_add
import Submission.Commons.Algebra.MvPolynomial.linearIndependent_iff_exists_wronskian

/-!
# The elementary elimination step (Schmidt's specialization)

Abstract core of Schmidt's specialization (Evertse's proof of Lemma 24, the non-vanishing
lemma): the operation "extract the lowest coefficient in one variable", its interaction with
substitution and differentiation, and the resulting iteration lemma.
-/

open scoped BigOperators
open MvPolynomial

namespace Submission.Subspace

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The lowest power of `X y` occurring in `F` (`0` for `F = 0`). -/
noncomputable def lowestDeg (y : σ) (F : MvPolynomial σ K) : ℕ :=
  sInf {n : ℕ | ∃ u ∈ F.support, u y = n}

/-- The polynomial obtained from `F` by dividing out the *lowest* power of `X y` occurring in
`F`. -/
noncomputable def lowestCoeff (y : σ) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ u ∈ F.support.filter (fun u => u y = lowestDeg y F),
    MvPolynomial.monomial (u - Finsupp.single y (lowestDeg y F)) (MvPolynomial.coeff u F)

variable {y : σ} {F : MvPolynomial σ K}

lemma lowestDeg_le (h : F.support.Nonempty) {u : σ →₀ ℕ} (hu : u ∈ F.support) :
    lowestDeg y F ≤ u y :=
  Nat.sInf_le ⟨u, hu, rfl⟩

lemma lowestDeg_mem (h : F.support.Nonempty) :
    ∃ u ∈ F.support, u y = lowestDeg y F := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨v, hv, hvu⟩ := Nat.sInf_mem (s := {n : ℕ | ∃ w ∈ F.support, w y = n})
    ⟨u y, u, hu, rfl⟩
  exact ⟨v, hv, hvu⟩

/-- Every monomial of `lowestCoeff y F` has the form `w - s • e_y` for `w` a monomial of `F`. -/
lemma mem_support_lowestCoeff {u : σ →₀ ℕ} (hu : u ∈ (lowestCoeff y F).support) :
    ∃ w ∈ F.support, w y = lowestDeg y F ∧ u = w - Finsupp.single y (lowestDeg y F) := by
  classical
  by_cases h : F.support.Nonempty
  · have hcoeff : (lowestCoeff y F).coeff u ≠ 0 := MvPolynomial.mem_support_iff.mp hu
    rw [lowestCoeff, MvPolynomial.coeff_sum] at hcoeff
    obtain ⟨w, hw, hwne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
    rw [Finset.mem_filter] at hw
    have hmem : u ∈ (MvPolynomial.monomial
        (w - Finsupp.single y (lowestDeg y F)) (MvPolynomial.coeff w F)).support :=
      MvPolynomial.mem_support_iff.mpr hwne
    have hsub := MvPolynomial.support_monomial_subset hmem
    rw [Finset.mem_singleton] at hsub
    exact ⟨w, hw.1, hw.2, hsub⟩
  · have hF : F = 0 := by
      by_contra hne
      exact h (MvPolynomial.support_nonempty.mpr hne)
    rw [hF, lowestCoeff] at hu
    simp at hu

/-- Every monomial of `lowestCoeff y F` is free of `y`. -/
lemma lowestCoeff_y_free : ∀ u ∈ (lowestCoeff y F).support, u y = 0 := by
  intro u hu
  obtain ⟨w, -, hwy, hw⟩ := mem_support_lowestCoeff hu
  rw [hw]
  simp [hwy]

/-- A polynomial none of whose monomials involves the variables of `S`. -/
def FreeOf (S : Finset σ) (F : MvPolynomial σ K) : Prop :=
  ∀ u ∈ F.support, ∀ z ∈ S, u z = 0

lemma FreeOf.mono {S S' : Finset σ} {F : MvPolynomial σ K} (h : S' ⊆ S) (hF : FreeOf S F) :
    FreeOf S' F := fun u hu z hz => hF u hu z (h hz)

lemma freeOf_insert_lowestCoeff {z : σ} {S : Finset σ} (hz : z ∉ S) (hF : FreeOf S F) :
    FreeOf (insert z S) (lowestCoeff z F) := by
  intro u hu z' hz'
  obtain ⟨w, hw, hwy, hw'⟩ := mem_support_lowestCoeff hu
  rw [Finset.mem_insert] at hz'
  rcases hz' with rfl | hz'
  · rw [hw']
    simp [hwy]
  · have hne : z' ≠ z := fun hh => hz (hh ▸ hz')
    simpa [hw', Finsupp.single_eq_of_ne (a := z) (a' := z') hne] using hF w hw z' hz'

section Factor

variable {y : σ}

/-- `Finsupp` helper: `s • e_y + (u - s • e_y) = u` when `s ≤ u y`. -/
lemma single_add_tsub {u : σ →₀ ℕ} {s : ℕ} (h : s ≤ u y) :
    Finsupp.single y s + (u - Finsupp.single y s) = u := by
  ext z
  rcases eq_or_ne z y with rfl | hz
  · simp [h]
  · simp [Finsupp.single_eq_of_ne hz]

lemma X_pow_mul_monomial_tsub {u : σ →₀ ℕ} {s : ℕ} (h : s ≤ u y) (a : K) :
    MvPolynomial.X y ^ s * MvPolynomial.monomial (u - Finsupp.single y s) a =
      MvPolynomial.monomial u a := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul,
    single_add_tsub h]

/-- **The factorization at the lowest `y`-power**: for `F ≠ 0` there is `q` with
`F = X y ^ s * (lowestCoeff y F + X y * q)`, where `s = lowestDeg y F`. -/
lemma lowestCoeff_factor (h : F ≠ 0) :
    ∃ q : MvPolynomial σ K, F = MvPolynomial.X y ^ (lowestDeg y F) *
      (lowestCoeff y F + MvPolynomial.X y * q) := by
  classical
  have hmem : F.support.Nonempty := MvPolynomial.support_nonempty.mpr h
  have hsplit : ∀ u ∈ F.support, u y = lowestDeg y F ∨ lowestDeg y F < u y := by
    intro u hu
    rcases lt_or_eq_of_le (lowestDeg_le hmem hu) with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl heq.symm
  have hA : MvPolynomial.X y ^ (lowestDeg y F) * lowestCoeff y F =
      ∑ u ∈ F.support.filter (fun u => u y = lowestDeg y F),
        MvPolynomial.monomial u (MvPolynomial.coeff u F) := by
    rw [lowestCoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_filter] at hu
    exact X_pow_mul_monomial_tsub hu.2.ge _
  have hB : MvPolynomial.X y ^ (lowestDeg y F + 1) *
      (∑ u ∈ F.support.filter (fun u => lowestDeg y F < u y),
        MvPolynomial.monomial (u - Finsupp.single y (lowestDeg y F + 1))
          (MvPolynomial.coeff u F)) =
      ∑ u ∈ F.support.filter (fun u => lowestDeg y F < u y),
        MvPolynomial.monomial u (MvPolynomial.coeff u F) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_filter] at hu
    exact X_pow_mul_monomial_tsub (by omega : lowestDeg y F + 1 ≤ u y) _
  have hdisj : Disjoint (F.support.filter (fun u => u y = lowestDeg y F))
      (F.support.filter (fun u => lowestDeg y F < u y)) := by
    rw [Finset.disjoint_filter]
    exact fun u _ h1 h2 => absurd h2 (by omega)
  have hsum : F = (∑ u ∈ F.support.filter (fun u => u y = lowestDeg y F),
        MvPolynomial.monomial u (MvPolynomial.coeff u F)) +
      ∑ u ∈ F.support.filter (fun u => lowestDeg y F < u y),
        MvPolynomial.monomial u (MvPolynomial.coeff u F) := by
    conv_lhs => rw [MvPolynomial.as_sum F]
    rw [← Finset.sum_union hdisj]
    refine Finset.sum_subset (fun u hu => ?_) (fun u hu hnu => ?_)
    · rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hsplit u hu with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
    · rw [MvPolynomial.notMem_support_iff.mp hnu, MvPolynomial.monomial_zero]
  refine ⟨∑ u ∈ F.support.filter (fun u => lowestDeg y F < u y),
      MvPolynomial.monomial (u - Finsupp.single y (lowestDeg y F + 1))
        (MvPolynomial.coeff u F), ?_⟩
  have key : MvPolynomial.X y ^ (lowestDeg y F) *
        (lowestCoeff y F + MvPolynomial.X y *
          (∑ u ∈ F.support.filter (fun u => lowestDeg y F < u y),
            MvPolynomial.monomial (u - Finsupp.single y (lowestDeg y F + 1))
              (MvPolynomial.coeff u F))) =
      (∑ u ∈ F.support.filter (fun u => u y = lowestDeg y F),
        MvPolynomial.monomial u (MvPolynomial.coeff u F)) +
      ∑ u ∈ F.support.filter (fun u => lowestDeg y F < u y),
        MvPolynomial.monomial u (MvPolynomial.coeff u F) := by
    rw [mul_add, ← mul_assoc, ← pow_succ, hA, hB]
  rw [key, ← hsum]

end Factor

section Commute

variable {y : σ}

/-- A `pderiv` in a variable other than `y` kills `X y ^ s`. -/
lemma pderiv_X_pow_of_ne {z : σ} (hz : z ≠ y) (s : ℕ) :
    MvPolynomial.pderiv z (MvPolynomial.X y ^ s : MvPolynomial σ K) = 0 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [pow_succ, MvPolynomial.pderiv_mul, ih, MvPolynomial.pderiv_X_of_ne (R := K) hz.symm]
      ring

lemma pderiv_X_pow_mul {z : σ} (hz : z ≠ y) (s : ℕ) (H : MvPolynomial σ K) :
    MvPolynomial.pderiv z (MvPolynomial.X y ^ s * H) =
      MvPolynomial.X y ^ s * MvPolynomial.pderiv z H := by
  rw [MvPolynomial.pderiv_mul, pderiv_X_pow_of_ne hz, zero_mul, zero_add]

lemma pderivIter_single_X_pow_mul {z : σ} (hz : z ≠ y) (c s : ℕ) (H : MvPolynomial σ K) :
    Commons.Algebra.MvPolynomial.pderivIter (Finsupp.single z c)
        (MvPolynomial.X y ^ s * H) =
      MvPolynomial.X y ^ s *
        Commons.Algebra.MvPolynomial.pderivIter (Finsupp.single z c) H := by
  have h0 := (Commons.Algebra.MvPolynomial.pderivIter_properties (R := K) (σ := σ)).1
  have hsingle := (Commons.Algebra.MvPolynomial.pderivIter_properties (R := K) (σ := σ)).2.1
  induction c with
  | zero => rw [Finsupp.single_zero, h0, h0]
  | succ c ih =>
      have h1 : Finsupp.single z (c + 1) = Finsupp.single z c + Finsupp.single z 1 :=
        Finsupp.single_add z c 1
      have key : Commons.Algebra.MvPolynomial.pderivIter (Finsupp.single z 1)
            (Commons.Algebra.MvPolynomial.pderivIter (Finsupp.single z c) H) =
          Commons.Algebra.MvPolynomial.pderivIter (Finsupp.single z c +
            Finsupp.single z 1) H :=
        (Commons.Algebra.MvPolynomial.pderivIter_add (Finsupp.single z c)
          (Finsupp.single z 1) H).symm
      rw [h1, Commons.Algebra.MvPolynomial.pderivIter_add, ih, hsingle, pderiv_X_pow_mul hz,
        ← hsingle, key]

/-- Iterated derivatives in variables other than `y` commute with multiplication by `X y ^ s`. -/
lemma pderivIter_X_pow_mul (s : ℕ) (α : σ →₀ ℕ) (hα : α y = 0) (G : MvPolynomial σ K) :
    Commons.Algebra.MvPolynomial.pderivIter α (MvPolynomial.X y ^ s * G) =
      MvPolynomial.X y ^ s * Commons.Algebra.MvPolynomial.pderivIter α G := by
  have h0 := (Commons.Algebra.MvPolynomial.pderivIter_properties (R := K) (σ := σ)).1
  refine Finsupp.induction₂ (motive := fun α => α y = 0 →
      Commons.Algebra.MvPolynomial.pderivIter α (MvPolynomial.X y ^ s * G) =
        MvPolynomial.X y ^ s * Commons.Algebra.MvPolynomial.pderivIter α G)
    α ?_ ?_ hα
  · intro _
    rw [h0, h0]
  · intro z c f _ _ ih hα
    have hzy : z ≠ y := by
      intro hzy
      subst hzy
      rw [Finsupp.add_apply, Finsupp.single_eq_same] at hα
      omega
    have hfz : f y = 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hzy)] at hα
      simpa using hα
    rw [Commons.Algebra.MvPolynomial.pderivIter_add, ih hfz,
      pderivIter_single_X_pow_mul hzy c s, ← Commons.Algebra.MvPolynomial.pderivIter_add]

end Commute

section Rho

variable {y : σ}

/-- The substitution sending `X y` to `0` and fixing all other variables. -/
noncomputable def rho (y : σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval (fun z : σ => if z = y then (0 : MvPolynomial σ K) else MvPolynomial.X z)

@[simp]
lemma rho_X_self : rho y (MvPolynomial.X y : MvPolynomial σ K) = 0 := by
  rw [rho, MvPolynomial.aeval_X]
  simp

lemma rho_X_of_ne {z : σ} (hz : z ≠ y) :
    rho y (MvPolynomial.X z : MvPolynomial σ K) = MvPolynomial.X z := by
  rw [rho, MvPolynomial.aeval_X]
  simp [hz]

end Rho

section Iter

open Commons.Algebra.MvPolynomial

/-- The elimination iteration: successively divide out the lowest power of each variable. -/
noncomputable def elimF : List σ → MvPolynomial σ K → MvPolynomial σ K
  | [], F => F
  | y :: ys, F => elimF ys (lowestCoeff y F)

/-- The corresponding substitution: compose the "set to zero" maps. -/
noncomputable def elimRho (ys : List σ) (Φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  ys.foldl (fun Ψ y => (rho y).comp Ψ) Φ

variable {y : σ}

variable {y : σ}

/-- The coefficient of `F` at the lowest `y`-power is a coefficient of `lowestCoeff y F`. -/
lemma coeff_lowestCoeff_of_mem {u : σ →₀ ℕ} (hu : u ∈ F.support) (huy : u y = lowestDeg y F) :
    (lowestCoeff y F).coeff (u - Finsupp.single y (lowestDeg y F)) =
      MvPolynomial.coeff u F := by
  classical
  have hu' : u ∈ F.support.filter (fun v => v y = lowestDeg y F) :=
    Finset.mem_filter.mpr ⟨hu, huy⟩
  rw [lowestCoeff, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single u]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro w hw hne
    rw [Finset.mem_filter] at hw
    rw [MvPolynomial.coeff_monomial,
      if_neg (fun hcontra => hne (by
        rw [← single_add_tsub (le_of_eq hw.2.symm), ← single_add_tsub (le_of_eq huy.symm),
          hcontra]))]
  · intro hnot
    exact absurd hu' hnot
lemma lowestCoeff_ne_zero (h : F ≠ 0) : lowestCoeff y F ≠ 0 := by
  classical
  obtain ⟨u, hu, huy⟩ := lowestDeg_mem (MvPolynomial.support_nonempty.mpr h)
  intro h0
  have hc := coeff_lowestCoeff_of_mem hu huy
  rw [h0, MvPolynomial.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp hu) hc.symm

end Iter


/-- **The elimination iteration.**  Suppose `Φ (∂^α F) = 0` where `Φ` is a substitution fixing
every variable of the list `ys` and `α` is supported off `ys`.  Then, after dividing out the
lowest powers of the variables of `ys` successively, one still has
`(elimRho ys Φ) (∂^α (elimF ys F)) = 0`, and the resulting polynomial is nonzero. -/
theorem elim_invariant (ys : List σ) (α : σ →₀ ℕ) (F : MvPolynomial σ K)
    (Φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (hF : F ≠ 0) (hnd : ys.Nodup)
    (hfix : ∀ z ∈ ys, Φ (MvPolynomial.X z) = MvPolynomial.X z)
    (hα : ∀ z ∈ ys, α z = 0) (h : Φ (Commons.Algebra.MvPolynomial.pderivIter α F) = 0) :
    elimF ys F ≠ 0 ∧
      elimRho ys Φ (Commons.Algebra.MvPolynomial.pderivIter α (elimF ys F)) = 0 := by
  induction ys generalizing F Φ with
  | nil => exact ⟨hF, by simpa only [elimF, elimRho, List.foldl_nil] using h⟩
  | cons y ys ih =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hy_notin, hnd'⟩ := hnd
      have hF' : lowestCoeff y F ≠ 0 := lowestCoeff_ne_zero hF
      obtain ⟨q, hfac⟩ := lowestCoeff_factor (y := y) hF
      have hαy : α y = 0 := hα y List.mem_cons_self
      have hcomm : Commons.Algebra.MvPolynomial.pderivIter α F =
          MvPolynomial.X y ^ (lowestDeg y F) *
          (Commons.Algebra.MvPolynomial.pderivIter α (lowestCoeff y F) +
            MvPolynomial.X y * Commons.Algebra.MvPolynomial.pderivIter α q) := by
        conv_lhs => rw [hfac]
        rw [pderivIter_X_pow_mul (lowestDeg y F) α hαy,
          Commons.Algebra.MvPolynomial.pderivIter_add_apply]
        rw [show Commons.Algebra.MvPolynomial.pderivIter α (MvPolynomial.X y * q) =
            MvPolynomial.X y * Commons.Algebra.MvPolynomial.pderivIter α q from by
          simpa using pderivIter_X_pow_mul 1 α hαy q]
      have h2 : Φ (Commons.Algebra.MvPolynomial.pderivIter α (lowestCoeff y F) +
          MvPolynomial.X y * Commons.Algebra.MvPolynomial.pderivIter α q) = 0 := by
        have h1 := h
        rw [hcomm, map_mul, map_pow, hfix y List.mem_cons_self] at h1
        rcases mul_eq_zero.mp h1 with h1 | h1
        · exact absurd h1 (pow_ne_zero (lowestDeg y F) (MvPolynomial.X_ne_zero y))
        · exact h1
      have h3 : ((rho y).comp Φ)
          (Commons.Algebra.MvPolynomial.pderivIter α (lowestCoeff y F)) = 0 := by
        have h4 : Φ (Commons.Algebra.MvPolynomial.pderivIter α (lowestCoeff y F)) +
            Φ (MvPolynomial.X y) *
              Φ (Commons.Algebra.MvPolynomial.pderivIter α q) = 0 := by
          simpa only [map_add, map_mul] using h2
        have h5 : (rho y) (Φ (Commons.Algebra.MvPolynomial.pderivIter α (lowestCoeff y F))) +
            (rho y) (Φ (MvPolynomial.X y)) *
              (rho y) (Φ (Commons.Algebra.MvPolynomial.pderivIter α q)) = 0 := by
          have := congrArg (rho y) h4
          simpa only [map_add, map_mul, map_zero] using this
        have hX : (rho y) (Φ (MvPolynomial.X y)) = 0 := by
          rw [hfix y List.mem_cons_self, rho_X_self]
        simpa only [AlgHom.comp_apply, hX, zero_mul, add_zero] using h5
      have hfix' : ∀ z ∈ ys, ((rho y).comp Φ) (MvPolynomial.X z) = MvPolynomial.X z := by
        intro z hz
        rw [AlgHom.comp_apply, hfix z (List.mem_cons_of_mem y hz)]
        exact rho_X_of_ne (fun hzy => hy_notin (hzy ▸ hz))
      have hα' : ∀ z ∈ ys, α z = 0 := fun z hz => hα z (List.mem_cons_of_mem y hz)
      obtain ⟨hne, hinv⟩ := ih (lowestCoeff y F) ((rho y).comp Φ) hF' hnd' hfix' hα' h3
      refine ⟨?_, ?_⟩
      · simpa only [elimF] using hne
      · rw [elimF, elimRho, List.foldl_cons, ← elimRho]
        exact hinv


section FreeProps

open Commons.Algebra.MvPolynomial

/-- `FreeOf` is well behaved with respect to unions. -/
lemma freeOf_union_iff {S S' : Finset σ} {F : MvPolynomial σ K} :
    FreeOf (S ∪ S') F ↔ FreeOf S F ∧ FreeOf S' F := by
  constructor
  · intro h
    exact ⟨h.mono Finset.subset_union_left, h.mono Finset.subset_union_right⟩
  · rintro ⟨h1, h2⟩ u hu z hz
    rw [Finset.mem_union] at hz
    exact hz.elim (h1 u hu z) (h2 u hu z)

/-- The elimination iteration keeps the polynomial nonzero. -/
lemma elimF_ne_zero : ∀ (ys : List σ) (F : MvPolynomial σ K), F ≠ 0 → elimF ys F ≠ 0
  | [], F, hF => by simpa only [elimF] using hF
  | y :: ys, F, hF => elimF_ne_zero ys (lowestCoeff y F) (lowestCoeff_ne_zero hF)

/-- The elimination iteration keeps a polynomial free of a set of variables, provided the list
does not meet that set. -/
theorem freeOf_elimF (ys : List σ) (F : MvPolynomial σ K) (S : Finset σ) (hys : ys.Nodup)
    (hnd : Disjoint ys.toFinset S) (hF : FreeOf S F) :
    FreeOf S (elimF ys F) ∧ FreeOf ys.toFinset (elimF ys F) := by
  induction ys generalizing F S with
  | nil => exact ⟨by simpa only [elimF] using hF, fun u _ z hz => by simp at hz⟩
  | cons y ys ih =>
      rw [List.nodup_cons] at hys
      obtain ⟨hyys, hys'⟩ := hys
      rw [List.toFinset_cons, Finset.disjoint_insert_left] at hnd
      obtain ⟨hyS, hndS⟩ := hnd
      have hnd' : Disjoint (ys.toFinset) (insert y S) := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact fun h => hyys (List.mem_toFinset.mp (h ▸ ha))
        · exact Finset.disjoint_iff_ne.mp hndS a ha b hb
      have hFy : FreeOf (insert y S) (lowestCoeff y F) :=
        freeOf_insert_lowestCoeff (S := S) hyS hF
      obtain ⟨h1, h2⟩ := ih (lowestCoeff y F) (insert y S) hys' hnd' hFy
      refine ⟨?_, ?_⟩
      · simpa only [elimF] using h1.mono (Finset.subset_insert y S)
      · rw [elimF, List.toFinset_cons, Finset.insert_eq]
        exact freeOf_union_iff.mpr
          ⟨h1.mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self y S)), h2⟩

end FreeProps


section Kill

open Commons.Algebra.MvPolynomial

/-- The substitution killing all variables of a finite set. -/
noncomputable def kill (S : Finset σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval (fun z : σ => if z ∈ S then 0 else MvPolynomial.X z)

lemma kill_X_of_mem {S : Finset σ} {z : σ} (hz : z ∈ S) : kill (K := K) S (MvPolynomial.X z) = 0 := by
  rw [kill, MvPolynomial.aeval_X]; simp [hz]

lemma kill_X_of_notMem {S : Finset σ} {z : σ} (hz : z ∉ S) :
    kill (K := K) S (MvPolynomial.X z) = MvPolynomial.X z := by
  rw [kill, MvPolynomial.aeval_X]; simp [hz]

lemma rho_eq_kill_singleton (y : σ) : rho (K := K) y = kill (K := K) ({y} : Finset σ) := by
  refine MvPolynomial.algHom_ext fun z => ?_
  by_cases hz : z = y
  · subst z
    rw [rho_X_self, kill_X_of_mem (Finset.mem_singleton_self y)]
  · rw [rho_X_of_ne hz, kill_X_of_notMem (by simpa [Finset.mem_singleton] using hz)]

lemma kill_empty : kill (K := K) (∅ : Finset σ) = AlgHom.id K (MvPolynomial σ K) := by
  refine MvPolynomial.algHom_ext fun z => ?_
  rw [kill_X_of_notMem (Finset.notMem_empty z)]
  rfl

lemma kill_comp_kill (S T : Finset σ) :
    (kill (K := K) T).comp (kill (K := K) S) = kill (K := K) (S ∪ T) := by
  refine MvPolynomial.algHom_ext fun z => ?_
  rw [AlgHom.comp_apply]
  by_cases hzS : z ∈ S
  · rw [kill_X_of_mem hzS, map_zero, kill_X_of_mem (Finset.mem_union_left T hzS)]
  · rw [kill_X_of_notMem hzS]
    by_cases hzT : z ∈ T
    · rw [kill_X_of_mem hzT, kill_X_of_mem (Finset.mem_union_right S hzT)]
    · rw [kill_X_of_notMem hzT, kill_X_of_notMem (by simp [hzS, hzT])]

/-- The elimination substitution is the composition of the "kill" substitution with the initial
substitution. -/
theorem elimRho_eq_kill (ys : List σ) (Φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) :
    elimRho ys Φ = (kill (K := K) ys.toFinset).comp Φ := by
  induction ys generalizing Φ with
  | nil => rw [elimRho, List.foldl_nil, List.toFinset_nil, kill_empty, AlgHom.id_comp]
  | cons y ys ih =>
      rw [elimRho, List.foldl_cons, ← elimRho, ih, ← AlgHom.comp_assoc, rho_eq_kill_singleton,
        kill_comp_kill, List.toFinset_cons, Finset.insert_eq, Finset.union_comm]

end Kill

end Submission.Subspace



