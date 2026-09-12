import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Algebra.Polynomial.coeff_comp_X_sub_C
import Submission.Commons.Algebra.Polynomial.coeff_nonneg_of_eventually_eval_nonneg

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MvPolynomial

namespace Commons.RingTheory.Ideal.Hilbert

noncomputable section

/-! ## General linear-algebra helper lemmas -/

section General

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Rank-nullity in the form used below. -/
lemma finrank_map_add_finrank_inf_ker (f : M →ₗ[k] N) (V : Submodule k M) [Module.Finite k ↥V] :
    Module.finrank k ↥(Submodule.map f V) + Module.finrank k ↥(V ⊓ f.ker)
      = Module.finrank k ↥V := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict V)
  rw [LinearMap.range_domRestrict] at h
  have hker : Module.finrank k ↥((f.domRestrict V).ker)
      = Module.finrank k ↥(V ⊓ f.ker) := by
    rw [LinearMap.ker_domRestrict]
    rw [← Submodule.finrank_map_subtype_eq V (Submodule.comap V.subtype f.ker),
      Submodule.map_comap_subtype]
  rwa [hker] at h

end General

section Algebra

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- The Hilbert-function value at a graded piece `V` of the quotient by an ideal `I`: the dimension
of the image of `V` in `R ⧸ I`. -/
def hilbertFun (I : Ideal R) (V : Submodule k R) : ℕ :=
  Module.finrank k ↥(Submodule.map (I.mkQ.restrictScalars k) V)

/-- The Hilbert-function value is the dimension of `V` minus the dimension of `V ⊓ I`. -/
lemma hilbertFun_eq_sub (I : Ideal R) (V : Submodule k R) [Module.Finite k ↥V] :
    hilbertFun I V = Module.finrank k ↥V - Module.finrank k ↥(V ⊓ I.restrictScalars k) := by
  have h := finrank_map_add_finrank_inf_ker (I.mkQ.restrictScalars k) V
  rw [show (I.mkQ.restrictScalars k).ker = I.restrictScalars k from ?_] at h
  · exact Nat.eq_sub_of_add_eq h
  · rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]

/-- The Hilbert function is antitone in the ideal. -/
lemma hilbertFun_anti {I J : Ideal R} (hIJ : I ≤ J) (V : Submodule k R) [Module.Finite k ↥V] :
    hilbertFun J V ≤ hilbertFun I V := by
  rw [hilbertFun_eq_sub J V, hilbertFun_eq_sub I V]
  refine Nat.sub_le_sub_left ?_ _
  exact Submodule.finrank_mono (inf_le_inf_left V (Submodule.restrictScalars_mono k hIJ))

end Algebra

section Homogeneous

open MvPolynomial

variable {k : Type} [Field k] {m : ℕ}

/-- The minimal primes of an ideal are pairwise incomparable. -/
lemma not_le_of_mem_minimalPrimes {K : Ideal (MvPolynomial (Fin m) k)}
    {p q : ↥(K.minimalPrimes)} (h : p ≠ q) : ¬ (p.1 ≤ q.1) := by
  intro hle
  exact h (Subtype.ext (le_antisymm hle (q.2.2 p.2.1 hle)))

/-- A homogeneous ideal which is not contained in another ideal contains a homogeneous element
which is not in the second ideal. -/
lemma exists_isHomogeneous_mem_notMem {K J : Ideal (MvPolynomial (Fin m) k)}
    (hK : ∀ x ∈ K, ∀ j, MvPolynomial.homogeneousComponent j x ∈ K) (h : ¬ K ≤ J) :
    ∃ (u : MvPolynomial (Fin m) k) (e : ℕ), u.IsHomogeneous e ∧ u ∈ K ∧ u ∉ J := by
  obtain ⟨x, hxK, hxJ⟩ := Set.not_subset.mp h
  by_contra hcon
  push Not at hcon
  refine hxJ ?_
  rw [← MvPolynomial.sum_homogeneousComponent x]
  exact Ideal.sum_mem J fun j _ =>
    hcon (MvPolynomial.homogeneousComponent j x) j
      (MvPolynomial.homogeneousComponent_isHomogeneous j x) (hK x hxK j)

/-- For a homogeneous minimal prime `q` of a homogeneous ideal, there is a homogeneous element
which lies in every other minimal prime but not in `q`. -/
lemma exists_isHomogeneous_mem_forall_mem_notMem {K : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ q ∈ K.minimalPrimes, ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    [Fintype ↥(K.minimalPrimes)] (q : ↥(K.minimalPrimes)) :
    ∃ (u : MvPolynomial (Fin m) k) (e : ℕ), u.IsHomogeneous e ∧
      (∀ q' : ↥(K.minimalPrimes), q' ≠ q → u ∈ (q'.1 : Ideal _)) ∧ u ∉ (q.1 : Ideal _) := by
  classical
  haveI : (q.1 : Ideal (MvPolynomial (Fin m) k)).IsPrime := q.2.1.1
  have hnotle : ¬ (⨅ (q' : {q' : ↥(K.minimalPrimes) // q' ≠ q}),
        (q'.1.1 : Ideal (MvPolynomial (Fin m) k))) ≤ (q.1 : Ideal _) := by
    intro hle
    have hx : ∀ (q' : ↥(K.minimalPrimes)) (h : q' ≠ q),
        ∃ x : MvPolynomial (Fin m) k, x ∈ (q'.1 : Ideal _) ∧ x ∉ (q.1 : Ideal _) := by
      intro q' h
      obtain ⟨x, hx1, hx2⟩ := Set.not_subset.mp (not_le_of_mem_minimalPrimes (p := q') (q := q) h)
      exact ⟨x, hx1, hx2⟩
    let x : (i : {q' : ↥(K.minimalPrimes) // q' ≠ q}) → MvPolynomial (Fin m) k :=
      fun i => Classical.choose (hx i.1 i.2)
    have hxmem : ∀ i, x i ∈ (i.1.1 : Ideal _) := fun i => (Classical.choose_spec (hx i.1 i.2)).1
    have hxnot : ∀ i, x i ∉ (q.1 : Ideal _) := fun i => (Classical.choose_spec (hx i.1 i.2)).2
    have hmem : (∏ i, x i) ∈ (q.1 : Ideal _) := by
      refine hle (Ideal.mem_iInf.mpr (fun i => ?_))
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem x (Finset.mem_univ i)
      rw [hc]
      exact Ideal.mul_mem_right c (i.1.1) (hxmem i)
    have hnotmem : (∏ i, x i) ∉ (q.1 : Ideal _) := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact hxnot i hi
    exact hnotmem hmem
  obtain ⟨u, hu, huq⟩ : ∃ u, u ∈ (⨅ (q' : {q' : ↥(K.minimalPrimes) // q' ≠ q}),
      (q'.1.1 : Ideal (MvPolynomial (Fin m) k))) ∧ u ∉ (q.1 : Ideal _) := by
    by_contra h
    push Not at h
    exact hnotle fun x hx => h x hx
  have hex : ∃ j, MvPolynomial.homogeneousComponent j u ∉ (q.1 : Ideal _) := by
    by_contra h
    push Not at h
    refine huq ?_
    rw [← MvPolynomial.sum_homogeneousComponent u]
    exact Ideal.sum_mem _ fun j _ => h j
  obtain ⟨j, hj⟩ := hex
  refine ⟨MvPolynomial.homogeneousComponent j u, j,
    MvPolynomial.homogeneousComponent_isHomogeneous j u, ?_, hj⟩
  intro q' hq'
  exact hq q'.1 q'.2 u (Ideal.mem_iInf.mp hu ⟨q', hq'⟩) j

/-- **Key inequality.** If `D q` is the degree of a homogeneous element `u q` which lies in every
minimal prime of `K` except `q` (where it does not lie), then the sum of the Hilbert functions of the
minimal primes, shifted by `D q`, is bounded by the Hilbert function of the radical `⋂ q`. -/
lemma sum_hilbertFun_le_hilbertFun_sInf {K : Ideal (MvPolynomial (Fin m) k)}
    [Fintype ↥(K.minimalPrimes)] (D : ↥(K.minimalPrimes) → ℕ)
    (hu : ∀ q : ↥(K.minimalPrimes), ∃ u : MvPolynomial (Fin m) k, u.IsHomogeneous (D q) ∧
      (∀ q' : ↥(K.minimalPrimes), q' ≠ q → u ∈ (q'.1 : Ideal _)) ∧ u ∉ (q.1 : Ideal _))
    {t : ℕ} (hDt : ∀ q, D q ≤ t) :
    (∑ q : ↥(K.minimalPrimes),
        hilbertFun (q.1 : Ideal _) (MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))
      ≤ hilbertFun (sInf K.minimalPrimes) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
  classical
  choose u hu using hu
  set A : Ideal (MvPolynomial (Fin m) k) := sInf K.minimalPrimes with hA
  haveI hfin : ∀ s, Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k s) := fun s =>
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k s)
  -- the image of a degree `t - D q` piece under multiplication by `u q` lands in degree `t`
  have hmem_cod : ∀ (q : ↥(K.minimalPrimes))
      (x : ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))),
      A.mkQ (u q * (x : MvPolynomial (Fin m) k)) ∈
        Submodule.map (A.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
    intro q x
    refine Submodule.mem_map.mpr ⟨u q * (x : MvPolynomial (Fin m) k), ?_, rfl⟩
    have h3 : (u q * (x : MvPolynomial (Fin m) k)).IsHomogeneous (D q + (t - D q)) :=
      ((hu q).1).mul x.2
    rwa [Nat.add_sub_cancel' (hDt q)] at h3
  -- the component maps
  let comp : (q : ↥(K.minimalPrimes)) →
      ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)) →ₗ[k]
        (MvPolynomial (Fin m) k ⧸ A) :=
    fun q => (A.mkQ.restrictScalars k).comp
      (((LinearMap.mulLeft (MvPolynomial (Fin m) k) (u q)).restrictScalars k).comp
        (Submodule.subtype (MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))))
  have comp_apply : ∀ (q : ↥(K.minimalPrimes))
      (x : ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))),
      comp q x = A.mkQ (u q * (x : MvPolynomial (Fin m) k)) := by
    intro q x
    rfl
  let Ψ : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))) →ₗ[k] (MvPolynomial (Fin m) k ⧸ A) :=
    ∑ q : ↥(K.minimalPrimes), (comp q).comp (LinearMap.proj q)
  have Ψ_apply : ∀ w : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))),
      Ψ w = ∑ q, A.mkQ (u q * (w q : MvPolynomial (Fin m) k)) := by
    intro w
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun q _ => comp_apply q (w q))
  -- the range is contained in the degree `t` piece of `R ⧸ A`
  have hrange_le : Ψ.range ≤ Submodule.map (A.mkQ.restrictScalars k)
      (MvPolynomial.homogeneousSubmodule (Fin m) k t) := by
    rintro y ⟨w, rfl⟩
    rw [Ψ_apply w]
    exact Submodule.sum_mem _ (fun q _ => hmem_cod q (w q))
  -- the kernel is contained in the tuples with components in the corresponding minimal prime
  have hker_mem : ∀ (w : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))), Ψ w = 0 →
      ∀ q₀ : ↥(K.minimalPrimes), ((w q₀ : ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q₀))) :
        MvPolynomial (Fin m) k) ∈ (q₀.1 : Ideal _) := by
    intro w hw q₀
    haveI : (q₀.1 : Ideal (MvPolynomial (Fin m) k)).IsPrime := q₀.2.1.1
    have hsum0 : (∑ q, A.mkQ (u q * (w q : MvPolynomial (Fin m) k))) = 0 := by
      rw [← Ψ_apply w, hw]
    have hsum : (∑ q, u q * (w q : MvPolynomial (Fin m) k)) ∈ A := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [map_sum]
      exact hsum0
    have hmemA : (∑ q, u q * (w q : MvPolynomial (Fin m) k)) ∈ (q₀.1 : Ideal _) :=
      (sInf_le q₀.2 : A ≤ (q₀.1 : Ideal _)) hsum
    have hsplit : u q₀ * (w q₀ : MvPolynomial (Fin m) k)
        = (∑ q, u q * (w q : MvPolynomial (Fin m) k))
          - ∑ q ∈ Finset.univ.erase q₀, u q * (w q : MvPolynomial (Fin m) k) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q₀)]
      abel
    have hmem2 : (∑ q ∈ Finset.univ.erase q₀, u q * (w q : MvPolynomial (Fin m) k))
        ∈ (q₀.1 : Ideal _) := by
      refine Ideal.sum_mem _ fun q hq => ?_
      have hne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
      have hmem : u q ∈ (q₀.1 : Ideal _) := (hu q).2.1 q₀ (Ne.symm hne)
      exact Ideal.mul_mem_right (w q : MvPolynomial (Fin m) k) (q₀.1) hmem
    have hprod : u q₀ * (w q₀ : MvPolynomial (Fin m) k) ∈ (q₀.1 : Ideal _) := by
      rw [hsplit]
      exact Ideal.sub_mem _ hmemA hmem2
    rcases Ideal.IsPrime.mem_or_mem q₀.2.1.1 hprod with h | h
    · exact absurd h (hu q₀).2.2
    · exact h
  -- the "kernel side": the inclusion of the tuples lying in the corresponding minimal prime
  let inc : ((q : ↥(K.minimalPrimes)) → ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)
        ⊓ (q.1).restrictScalars k)) →ₗ[k]
      ((q : ↥(K.minimalPrimes)) → ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))) :=
    LinearMap.pi (fun q => (Submodule.inclusion (inf_le_left)).comp (LinearMap.proj q))
  have hinc_inj : Function.Injective inc := by
    intro x y hxy
    funext q
    have h := congrFun (congrArg (fun (z : ((q : ↥(K.minimalPrimes)) →
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))) => fun q => (z q : MvPolynomial (Fin m) k)) hxy) q
    exact Subtype.ext h
  have hker_le : Ψ.ker ≤ inc.range := by
    intro w hw
    rw [LinearMap.mem_ker] at hw
    refine ⟨fun q => ⟨w q, (w q).2, hker_mem w hw q⟩, ?_⟩
    funext q
    rfl
  have hker_finrank : Module.finrank k ↥(Ψ.ker)
      ≤ ∑ q : ↥(K.minimalPrimes), Module.finrank k
          ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k) := by
    have hfin_inc : Module.finrank k ↥(inc.range)
        = Module.finrank k (((q : ↥(K.minimalPrimes)) →
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k))) := by
      have h := LinearMap.finrank_range_add_finrank_ker inc
      rw [show inc.ker = ⊥ from ?_] at h
      · simp only [finrank_bot, add_zero] at h; exact h
      · rw [Submodule.eq_bot_iff]
        intro x hx
        exact hinc_inj (by rw [map_zero, hx])
    calc Module.finrank k ↥(Ψ.ker) ≤ Module.finrank k ↥(inc.range) :=
          Submodule.finrank_mono hker_le
      _ = Module.finrank k (((q : ↥(K.minimalPrimes)) →
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k))) :=
          hfin_inc
      _ = ∑ q : ↥(K.minimalPrimes), Module.finrank k
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k) :=
          Module.finrank_pi_fintype k
  have hrange_finrank : Module.finrank k ↥(Ψ.range)
      ≤ Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t)
        - Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t ⊓ A.restrictScalars k) := by
    calc Module.finrank k ↥(Ψ.range)
        ≤ Module.finrank k ↥(Submodule.map (A.mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k t)) :=
          Submodule.finrank_mono hrange_le
      _ = Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t)
            - Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t ⊓ A.restrictScalars k) :=
          hilbertFun_eq_sub A (MvPolynomial.homogeneousSubmodule (Fin m) k t)
  have hrank := LinearMap.finrank_range_add_finrank_ker Ψ
  have hDom : Module.finrank k (((q : ↥(K.minimalPrimes)) →
      ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q))))
      = ∑ q : ↥(K.minimalPrimes), Module.finrank k
          ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)) :=
    Module.finrank_pi_fintype k
  have key : (∑ q : ↥(K.minimalPrimes), Module.finrank k
        ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))
      ≤ (∑ q : ↥(K.minimalPrimes), Module.finrank k
          ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q) ⊓ (q.1).restrictScalars k))
        + (Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t)
            - Module.finrank k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k t ⊓ A.restrictScalars k)) := by
    calc (∑ q : ↥(K.minimalPrimes), Module.finrank k
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))
        = Module.finrank k (((q : ↥(K.minimalPrimes)) →
            ↥(MvPolynomial.homogeneousSubmodule (Fin m) k (t - D q)))) := hDom.symm
      _ = Module.finrank k ↥(Ψ.ker) + Module.finrank k ↥(Ψ.range) := by
            rw [add_comm]; exact hrank.symm
      _ ≤ _ := add_le_add hker_finrank hrange_finrank
  rw [Finset.sum_congr rfl (fun q _ => hilbertFun_eq_sub (q.1 : Ideal _) _),
    hilbertFun_eq_sub A (MvPolynomial.homogeneousSubmodule (Fin m) k t)]
  rw [Finset.sum_tsub_distrib Finset.univ (fun q _ => Submodule.finrank_mono inf_le_left)]
  exact Nat.sub_le_iff_le_add.mpr (by rw [add_comm]; exact key)

end Homogeneous

end


/-- For a homogeneous ideal `K` all of whose minimal primes have the same dimension, the sum over
the minimal primes of the degree-coefficient of the Hilbert polynomial of the quotient by that prime
is at most the corresponding degree-coefficient of the Hilbert polynomial of `S ⧸ K`.
Here the "Hilbert polynomials" are provided by the hypotheses that the Hilbert functions are
eventually given by the polynomials `P` and `Pq`. -/
theorem sum_coeff_le_coeff_hilbertPoly {k : Type} [Field k] {m : ℕ}
    (K : Ideal (MvPolynomial (Fin m) k))
    (hK : ∀ x ∈ K, ∀ j, MvPolynomial.homogeneousComponent j x ∈ K)
    (hq : ∀ q ∈ K.minimalPrimes, ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (P : Polynomial ℚ)
    (hP : ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = P.eval (t : ℚ))
    (Pq : ↥(K.minimalPrimes) → Polynomial ℚ)
    (hPq : ∀ q, ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = (Pq q).eval (t : ℚ))
    (δ : ℕ) (hδ : ∀ q, (Pq q).natDegree = δ) (hPδ : P.natDegree ≤ δ)
    [Fintype ↥(K.minimalPrimes)] :
    (∑ q : ↥(K.minimalPrimes), (Pq q).coeff δ) ≤ P.coeff δ := by
  classical
  haveI hfin : ∀ s, Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k s) := fun s =>
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k s)
  -- for every minimal prime `q`, a homogeneous element lying in all the *other* minimal primes
  choose u e hue using fun q : ↥(K.minimalPrimes) =>
    exists_isHomogeneous_mem_forall_mem_notMem hq q
  -- the resulting inequality between Hilbert functions
  have hkey : ∀ t : ℕ, (∀ q : ↥(K.minimalPrimes), e q ≤ t) →
      (∑ q : ↥(K.minimalPrimes),
          Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k (t - e q))))
        ≤ Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k t)) := by
    intro t ht
    refine le_trans (sum_hilbertFun_le_hilbertFun_sInf e (fun q => ⟨u q, hue q⟩) ht) ?_
    exact hilbertFun_anti (le_sInf (fun q hq => hq.le)) _
  obtain ⟨N, hN⟩ := hP
  choose Nq hNq using hPq
  -- the inequality of Hilbert functions, evaluated at large `t`
  have hineq : ∃ T : ℕ, ∀ t ≥ T,
      (∑ q : ↥(K.minimalPrimes), (Pq q).eval ((t - e q : ℕ) : ℚ)) ≤ P.eval (t : ℚ) := by
    refine ⟨max N (Finset.univ.sup (fun q : ↥(K.minimalPrimes) => Nq q + e q)), fun t ht => ?_⟩
    have htN : N ≤ t := le_trans (le_max_left _ _) ht
    have hbound : ∀ q : ↥(K.minimalPrimes),
        Nq q + e q ≤ Finset.univ.sup (fun q : ↥(K.minimalPrimes) => Nq q + e q) :=
      fun q => Finset.le_sup (f := fun q : ↥(K.minimalPrimes) => Nq q + e q) (Finset.mem_univ q)
    have hsupT : Finset.univ.sup (fun q : ↥(K.minimalPrimes) => Nq q + e q) ≤ t :=
      le_trans (le_max_right _ _) ht
    have he_le : ∀ q : ↥(K.minimalPrimes), Nq q ≤ t - e q := fun q => by
      have := hbound q; have := hsupT; omega
    have he_t : ∀ q : ↥(K.minimalPrimes), e q ≤ t := fun q => by
      have := hbound q; have := hsupT; omega
    have hsum_eq : (∑ q : ↥(K.minimalPrimes), (Pq q).eval ((t - e q : ℕ) : ℚ))
        = ((∑ q : ↥(K.minimalPrimes), Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
            (MvPolynomial.homogeneousSubmodule (Fin m) k (t - e q))) : ℕ) : ℚ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun q _ => (hNq q (t - e q) (he_le q)).symm)
    rw [hsum_eq]
    have h1 : ((∑ q : ↥(K.minimalPrimes), Module.finrank k (Submodule.map ((q.1).mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k (t - e q))) : ℕ) : ℚ)
        ≤ ((Module.finrank k (Submodule.map (K.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℕ) : ℚ) := by
      exact_mod_cast hkey t he_t
    rwa [hN t htN] at h1
  obtain ⟨T, hT⟩ := hineq
  -- the polynomial whose values are the above sums
  set S : Polynomial ℚ := ∑ q : ↥(K.minimalPrimes),
    (Pq q).comp (Polynomial.X - Polynomial.C ((e q : ℕ) : ℚ)) with hS
  have hS_eval : ∀ n : ℕ, (∀ q : ↥(K.minimalPrimes), e q ≤ n) → S.eval (n : ℚ)
      = ∑ q : ↥(K.minimalPrimes), (Pq q).eval ((n - e q : ℕ) : ℚ) := by
    intro n hn
    rw [hS, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl (fun q _ => by
      rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        Nat.cast_sub (hn q)])
  have hpoly : ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n → 0 ≤ (P - S).eval (n : ℚ) := by
    refine ⟨max T (Finset.univ.sup e), fun n hn => ?_⟩
    have hnT : T ≤ n := le_trans (le_max_left _ _) hn
    have hne : ∀ q : ↥(K.minimalPrimes), e q ≤ n := fun q =>
      le_trans (Finset.le_sup (f := e) (Finset.mem_univ q)) (le_trans (le_max_right _ _) hn)
    rw [Polynomial.eval_sub, hS_eval n hne]
    exact sub_nonneg.mpr (hT n hnT)
  have hdeg : (P - S).natDegree ≤ δ := by
    refine le_trans (Polynomial.natDegree_sub_le P S) (max_le hPδ ?_)
    rw [hS]
    refine le_trans (Polynomial.natDegree_sum_le Finset.univ _) ?_
    refine Finset.sup_le (fun q _ => ?_)
    refine le_trans Polynomial.natDegree_comp_le ?_
    rw [Polynomial.natDegree_X_sub_C, mul_one]
    exact le_of_eq (hδ q)
  have hcoeff : 0 ≤ (P - S).coeff δ :=
    Commons.Algebra.Polynomial.coeff_nonneg_of_eventually_eval_nonneg hdeg hpoly
  have hScoeff : S.coeff δ = ∑ q : ↥(K.minimalPrimes), (Pq q).coeff δ := by
    rw [hS, Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl (fun q _ =>
      Commons.Algebra.Polynomial.coeff_comp_X_sub_C (Pq q) (((e q : ℕ) : ℚ)) (le_of_eq (hδ q)))
  rw [Polynomial.coeff_sub, hScoeff, sub_nonneg] at hcoeff
  exact hcoeff

end Commons.RingTheory.Ideal.Hilbert