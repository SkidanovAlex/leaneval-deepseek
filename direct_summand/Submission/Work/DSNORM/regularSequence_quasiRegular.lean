import Mathlib
import Submission.Work.DSNORM.PolynomialAux

/-!
# Quasi-regularity of a weakly regular sequence (Stacks 00LN, tag 00LN)

A regular sequence `f : Fin c → R` is quasi-regular: a form `F` of degree `n` with
`F(f) ∈ (f)^(n+1)` has all its coefficients in `(f)`.

The proof is the induction of Stacks 00LN: peel the last element `x = f_c` (which is a
nonzerodivisor modulo the ideal of the previous ones), decompose `F` by its degree in `X_c`
and run an inner induction on that degree.
-/

open scoped Pointwise

namespace Work.DSNORM

/-! ## Elementary complements -/

/-- `Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f)`. -/
private theorem ideal_ofList_ofFn {R : Type*} [CommRing R] {c : ℕ} (f : Fin c → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  rw [Ideal.ofList]
  congr 1
  ext r
  exact List.mem_ofFn.trans Set.mem_range.symm

/-- For an ideal `I` of `R`, viewed as a submodule of `R`, `I • ⊤ = I`. -/
private theorem ideal_smul_top {R : Type*} [CommRing R] (I : Ideal R) :
    I • (⊤ : Submodule R R) = (I : Submodule R R) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.smul_le]
    intro r hr m _
    rw [smul_eq_mul]
    exact Ideal.mul_mem_right m I hr
  · intro x hx
    have h := Submodule.smul_mem_smul hx (Submodule.mem_top : (1 : R) ∈ (⊤ : Submodule R R))
    simpa using h

/-- Every element of `I ^ k` is the value at `f` of a homogeneous polynomial of degree `k`
with coefficients in `R` (`I = Ideal.span (Set.range f)`). -/
private theorem exists_isHomogeneous_eval_eq_of_mem_pow {R : Type*} [CommRing R] {c : ℕ}
    (f : Fin c → R) {k : ℕ} {t : R} (ht : t ∈ (Ideal.span (Set.range f)) ^ k) :
    ∃ H : MvPolynomial (Fin c) R, H.IsHomogeneous k ∧ MvPolynomial.eval f H = t := by
  have hspan : (Ideal.span (Set.range f)) ^ k
      = Submodule.span R (((Set.range f) : Set R) ^ k) := by
    conv_lhs => rw [Ideal.span]
    exact Submodule.span_pow (Set.range f) k
  rw [hspan] at ht
  induction ht using Submodule.span_induction with
  | mem y hy =>
    rw [Set.mem_pow] at hy
    obtain ⟨g, hg⟩ := hy
    have hg' : ∀ i, f (Classical.choose (g i).2) = (g i : R) :=
      fun i => Classical.choose_spec (g i).2
    refine ⟨∏ i : Fin k, MvPolynomial.X (Classical.choose (g i).2), ?_, ?_⟩
    · have h1 : (∏ i : Fin k, MvPolynomial.X (Classical.choose (g i).2)).IsHomogeneous
          (∑ _i : Fin k, (1 : ℕ)) :=
        MvPolynomial.IsHomogeneous.prod Finset.univ _ _
          (fun i _ => MvPolynomial.isHomogeneous_X R _)
      simpa using h1
    · rw [map_prod]
      conv_rhs => rw [← hg, List.prod_ofFn]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [MvPolynomial.eval_X]
      exact hg' i
  | zero => exact ⟨0, MvPolynomial.isHomogeneous_zero (Fin c) R k, by simp⟩
  | add y z hy hz ihy ihz =>
    obtain ⟨P, hP, hPy⟩ := ihy
    obtain ⟨Q, hQ, hQz⟩ := ihz
    exact ⟨P + Q, hP.add hQ, by rw [map_add, hPy, hQz]⟩
  | smul r y hy ihy =>
    obtain ⟨P, hP, hPy⟩ := ihy
    exact ⟨MvPolynomial.C r * P, hP.C_mul r, by rw [map_mul, hPy, smul_eq_mul, MvPolynomial.eval_C]⟩

/-- If `t ∈ I ^ (n+1)` with `I = Ideal.span (Set.range f)`, then `t` is the value at `f` of a
homogeneous polynomial of degree `n` all of whose coefficients lie in `I`. -/
private theorem exists_homogeneous_coeff_mem_of_mem_pow {R : Type*} [CommRing R] {c : ℕ}
    (f : Fin c → R) {n : ℕ} {t : R} (ht : t ∈ (Ideal.span (Set.range f)) ^ (n + 1)) :
    ∃ H : MvPolynomial (Fin c) R, H.IsHomogeneous n ∧
      (∀ s, H.coeff s ∈ Ideal.span (Set.range f)) ∧ MvPolynomial.eval f H = t := by
  rw [pow_succ] at ht
  refine Submodule.mul_induction_on (C := fun r => ∃ H : MvPolynomial (Fin c) R,
    H.IsHomogeneous n ∧ (∀ s, H.coeff s ∈ Ideal.span (Set.range f))
      ∧ MvPolynomial.eval f H = r) ht ?_ ?_
  · intro a ha b hb
    obtain ⟨P, hP, hPeval⟩ := exists_isHomogeneous_eval_eq_of_mem_pow f ha
    exact ⟨MvPolynomial.C b * P, hP.C_mul b,
      fun s => by rw [MvPolynomial.coeff_C_mul]; exact Ideal.mul_mem_right (P.coeff s) _ hb,
      by rw [map_mul, hPeval, MvPolynomial.eval_C, mul_comm]⟩
  · intro x y hx hy
    obtain ⟨P, hP, hPc, hPe⟩ := hx
    obtain ⟨Q, hQ, hQc, hQe⟩ := hy
    exact ⟨P + Q, hP.add hQ,
      fun s => by rw [MvPolynomial.coeff_add]; exact Ideal.add_mem _ (hPc s) (hQc s),
      by rw [map_add, hPe, hQe]⟩

/-- If `x` is a nonzerodivisor on `R ⧸ I` and `x ^ k * a ∈ I`, then `a ∈ I`. -/
private theorem mem_of_pow_mul_mem {R : Type*} [CommRing R] {I : Ideal R} {x a : R}
    (hx : IsSMulRegular (R ⧸ I) x) (k : ℕ) (h : x ^ k * a ∈ I) : a ∈ I := by
  induction k with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    have hs : (x : R) • (((x ^ n) * a : R) : R ⧸ I) = ((x * ((x ^ n) * a) : R) : R ⧸ I) := by
      simpa using (Submodule.Quotient.mk_smul (p := I) x (x ^ n * a)).symm
    have h0 : (x : R) • (((x ^ n) * a : R) : R ⧸ I) = (x : R) • (0 : R ⧸ I) := by
      rw [hs, smul_zero, Ideal.Quotient.eq_zero_iff_mem]
      rw [pow_succ'] at h
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hx h0)

/-- The prefix of a weakly regular sequence is weakly regular, and the last element is a
nonzerodivisor modulo the ideal generated by the prefix. -/
private theorem isWeaklyRegular_init_and_isSMulRegular_last {R : Type*} [CommRing R] {c : ℕ}
    (f : Fin (c + 1) → R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (fun i : Fin c => f i.castSucc)) ∧
      IsSMulRegular (R ⧸ Ideal.span (Set.range fun i : Fin c => f i.castSucc))
        (f (Fin.last c)) := by
  have hsplit : RingTheory.Sequence.IsWeaklyRegular R
      ((List.ofFn fun i : Fin c => f i.castSucc) ++ [f (Fin.last c)]) := by
    rw [← List.concat_eq_append, ← List.ofFn_succ']
    exact hreg
  obtain ⟨h1, h2⟩ := (RingTheory.Sequence.isWeaklyRegular_append_iff R
    (List.ofFn fun i : Fin c => f i.castSucc) [f (Fin.last c)]).mp hsplit
  refine ⟨h1, ?_⟩
  have h3 : IsSMulRegular (R ⧸ (Ideal.ofList (List.ofFn fun i : Fin c => f i.castSucc) • ⊤))
      (f (Fin.last c)) :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mp h2
  have h4 : Ideal.ofList (List.ofFn fun i : Fin c => f i.castSucc) • (⊤ : Submodule R R)
      = Ideal.span (Set.range fun i : Fin c => f i.castSucc) := by
    rw [ideal_ofList_ofFn, ideal_smul_top]
  rwa [h4] at h3

/-! ## The main argument -/

/-- The inner induction of Stacks 00LN.

`f'` is the sequence of the previous elements, `x` the last one, `I` the ideal generated by
all of them (so `Ideal.span (Set.range f') ≤ I` and `x ∈ I`), and `ih` the (outer) induction
hypothesis for sequences of length `c`.

If `Gf e` is homogeneous of degree `n - e` for `e ≤ l`, and `∑_{e=0}^l (Gf e)(f') x^e = 0`,
then all coefficients of all `Gf e` (`e ≤ l`) lie in `I`. -/
private theorem inner_ind {R : Type*} [CommRing R] {c : ℕ} (n : ℕ) (f' : Fin c → R) (x : R)
    (I : Ideal R) (hI' : Ideal.span (Set.range f') ≤ I) (hxI : x ∈ I)
    (hreg' : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f'))
    (hxreg : IsSMulRegular (R ⧸ Ideal.span (Set.range f')) x)
    (ih : ∀ (g : Fin c → R), RingTheory.Sequence.IsWeaklyRegular R (List.ofFn g) →
      ∀ (m : ℕ) (F : MvPolynomial (Fin c) R), F.IsHomogeneous m →
        MvPolynomial.eval g F ∈ (Ideal.span (Set.range g)) ^ (m + 1) →
        ∀ s, F.coeff s ∈ Ideal.span (Set.range g)) :
    ∀ l, l ≤ n → ∀ (Gf : ℕ → MvPolynomial (Fin c) R),
      (∀ e ≤ l, (Gf e).IsHomogeneous (n - e)) →
      (∑ e ∈ Finset.range (l + 1), MvPolynomial.eval f' (Gf e) * x ^ e = 0) →
      ∀ e ≤ l, ∀ d, (Gf e).coeff d ∈ I := by
  intro l
  induction l with
  | zero =>
    intro _ Gf hGf hrel e he d
    have he0 : e = 0 := Nat.le_zero.mp he
    subst he0
    have hG0 : (Gf 0).IsHomogeneous n := by simpa using hGf 0 (le_refl 0)
    have hev : MvPolynomial.eval f' (Gf 0) = 0 := by
      have h1 := hrel
      rw [Finset.sum_range_succ, Finset.sum_range_zero] at h1
      simpa using h1
    exact hI' (ih f' hreg' n (Gf 0) hG0 (by rw [hev]; exact Submodule.zero_mem _) d)
  | succ l ihl =>
    intro hl Gf hGf hrel e he d
    -- `hl : l + 1 ≤ n`
    -- (b) values of the `Gf e` for `e ≤ l` lie in the right power of `Ideal.span (Set.range f')`
    have hgp : ∀ e ≤ l, MvPolynomial.eval f' (Gf e)
        ∈ (Ideal.span (Set.range f')) ^ (n - e) := by
      intro e he
      exact eval_mem_pow_of_isHomogeneous _ _ (fun i => Ideal.subset_span (Set.mem_range_self i))
        (hGf e (by omega))
    -- (c) the partial sum lies in `(Ideal.span (Set.range f')) ^ (n - l)`
    have hsumI : ∑ e ∈ Finset.range (l + 1), MvPolynomial.eval f' (Gf e) * x ^ e
        ∈ (Ideal.span (Set.range f')) ^ (n - l) := by
      refine Submodule.sum_mem _ fun e he => ?_
      rw [Finset.mem_range] at he
      have he1 : e ≤ l := by omega
      exact (Ideal.pow_le_pow_right (by omega : n - l ≤ n - e))
        (Ideal.mul_mem_right (x ^ e) _ (hgp e he1))
    -- (a) the relation with the last term removed
    have hA : (∑ e ∈ Finset.range (l + 1), MvPolynomial.eval f' (Gf e) * x ^ e)
        = -(MvPolynomial.eval f' (Gf (l + 1)) * x ^ (l + 1)) := by
      have h1 := hrel
      rw [Finset.sum_range_succ] at h1
      exact eq_neg_iff_add_eq_zero.mpr h1
    have hxy : x ^ (l + 1) * MvPolynomial.eval f' (Gf (l + 1))
        ∈ (Ideal.span (Set.range f')) ^ (n - l) := by
      have h2 : MvPolynomial.eval f' (Gf (l + 1)) * x ^ (l + 1)
          ∈ (Ideal.span (Set.range f')) ^ (n - l) := by
        have h3 : -(MvPolynomial.eval f' (Gf (l + 1)) * x ^ (l + 1))
            ∈ (Ideal.span (Set.range f')) ^ (n - l) := by
          rw [← hA]; exact hsumI
        simpa using neg_mem h3
      rwa [mul_comm] at h2
    -- (e) apply the outer induction hypothesis to `x^(l+1) * Gf (l+1)`
    have hhom : (MvPolynomial.C (x ^ (l + 1)) * Gf (l + 1)).IsHomogeneous (n - (l + 1)) :=
      MvPolynomial.IsHomogeneous.C_mul (hGf (l + 1) (le_refl _)) (x ^ (l + 1))
    have hval : MvPolynomial.eval f' (MvPolynomial.C (x ^ (l + 1)) * Gf (l + 1))
        ∈ (Ideal.span (Set.range f')) ^ (n - (l + 1) + 1) := by
      rw [map_mul, MvPolynomial.eval_C]
      rw [show n - (l + 1) + 1 = n - l from by omega]
      exact hxy
    have hstep : ∀ s, (MvPolynomial.C (x ^ (l + 1)) * Gf (l + 1)).coeff s
        ∈ Ideal.span (Set.range f') :=
      ih f' hreg' (n - (l + 1)) (MvPolynomial.C (x ^ (l + 1)) * Gf (l + 1)) hhom hval
    -- (f) hence the coefficients of `Gf (l+1)` lie in `Ideal.span (Set.range f')`
    have htopI : ∀ d, (Gf (l + 1)).coeff d ∈ Ideal.span (Set.range f') := by
      intro d
      have h1 := hstep d
      rw [MvPolynomial.coeff_C_mul] at h1
      exact mem_of_pow_mul_mem hxreg (l + 1) h1
    -- (g) the value `y` lies in `(Ideal.span (Set.range f')) ^ (n - l)`
    have hy : MvPolynomial.eval f' (Gf (l + 1)) ∈ (Ideal.span (Set.range f')) ^ (n - l) := by
      have h1 := eval_mem_pow_succ_of_coeff_mem (Ideal.span (Set.range f')) f'
        (fun i => Ideal.subset_span (Set.mem_range_self i)) (hGf (l + 1) (le_refl _)) htopI
      have he : n - (l + 1) + 1 = n - l := by omega
      rwa [he] at h1
    -- (h) lift `y` to a homogeneous polynomial of degree `n - l`
    obtain ⟨H0, hH0hom, hH0ev⟩ := exists_isHomogeneous_eval_eq_of_mem_pow f' hy
    -- (i) the modified family
    set Gtf : ℕ → MvPolynomial (Fin c) R :=
      fun e => Gf e + if e = l then MvPolynomial.C x * H0 else 0 with hGtfdef
    have hGtf_l : Gtf l = Gf l + MvPolynomial.C x * H0 := by
      rw [hGtfdef]; simp
    have hGtf_ne : ∀ e, e ≠ l → Gtf e = Gf e := by
      intro e he; rw [hGtfdef]; simp [he]
    -- (j) homogeneity of the modified family
    have hGtf_hom : ∀ e ≤ l, (Gtf e).IsHomogeneous (n - e) := by
      intro e hel
      by_cases hel' : e = l
      · rw [hel', hGtf_l]
        exact (hGf l (by omega)).add (MvPolynomial.IsHomogeneous.C_mul hH0hom x)
      · rw [hGtf_ne e hel']
        exact hGf e (by omega)
    -- (k) the relation for the modified family
    have hrel' : ∑ e ∈ Finset.range (l + 1), MvPolynomial.eval f' (Gtf e) * x ^ e = 0 := by
      have hterm : ∀ e ∈ Finset.range (l + 1),
          MvPolynomial.eval f' (Gtf e) * x ^ e
            = MvPolynomial.eval f' (Gf e) * x ^ e
              + (if e = l then (x * MvPolynomial.eval f' (Gf (l + 1))) * x ^ l else 0) := by
        intro e he
        rw [Finset.mem_range] at he
        by_cases hel : e = l
        · rw [hel, hGtf_l, map_add, map_mul, MvPolynomial.eval_C, hH0ev, if_pos rfl]
          ring
        · rw [hGtf_ne e hel, if_neg hel]
          ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        Finset.sum_ite_eq' (Finset.range (l + 1)) l
          (fun _ => (x * MvPolynomial.eval f' (Gf (l + 1))) * x ^ l),
        if_pos (Finset.mem_range.mpr (by omega))]
      rw [hA]
      ring
    -- (l) inner induction hypothesis
    have hres := ihl (by omega : l ≤ n) Gtf hGtf_hom hrel'
    -- (m) conclusion
    rcases lt_or_ge e (l + 1) with hlt | hge
    · have hel : e ≤ l := by omega
      by_cases hel' : e = l
      · rw [hel']
        have h1 := hres l le_rfl d
        have h2 : x * H0.coeff d ∈ I := Ideal.mul_mem_right (H0.coeff d) I hxI
        rw [show (Gf l).coeff d = (Gtf l).coeff d - x * H0.coeff d from by
          rw [hGtf_l, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul]; ring]
        exact Submodule.sub_mem I h1 h2
      · have h1 := hres e hel d
        rwa [hGtf_ne e hel'] at h1
    · have heq : e = l + 1 := by omega
      subst heq
      exact hI' (htopI d)

/-- **A weakly regular sequence is quasi-regular** (Stacks 00LN, Lemma 10.69.2): a form of
degree `n` whose value at the sequence lies in the `(n+1)`-st power of the ideal generated by
the sequence has all its coefficients in that ideal. -/
private theorem aux (c : ℕ) : ∀ (R : Type*) [CommRing R] (f : Fin c → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) →
    ∀ (n : ℕ) (F : MvPolynomial (Fin c) R), F.IsHomogeneous n →
      MvPolynomial.eval f F ∈ (Ideal.span (Set.range f)) ^ (n + 1) →
      ∀ s, F.coeff s ∈ Ideal.span (Set.range f) := by
  induction c with
  | zero =>
    intro R _ f _ n F _ h s
    have hrange : Set.range f = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨i, -⟩
      exact Fin.elim0 i
    have hI : Ideal.span (Set.range f) = (⊥ : Ideal R) := by rw [hrange, Ideal.span_empty]
    have hzero : F.coeff 0 = 0 := by
      have h1 : MvPolynomial.eval f F = F.coeff 0 := by
        conv_lhs => rw [MvPolynomial.eq_C_of_isEmpty F]
        rw [MvPolynomial.eval_C]
      have h2 : MvPolynomial.eval f F ∈ (⊥ : Ideal R) := by
        have hh := h
        rw [hI, Ideal.bot_pow (n := n + 1) (by omega)] at hh
        exact hh
      rw [← h1]
      exact (Submodule.mem_bot R).mp h2
    rw [hI, Submodule.mem_bot, show s = 0 from Finsupp.ext (fun i => Fin.elim0 i)]
    exact hzero
  | succ c ih =>
    intro R _ f hreg n F hF h s
    obtain ⟨hreg', hxreg⟩ := isWeaklyRegular_init_and_isSMulRegular_last f hreg
    set f' : Fin c → R := fun i => f i.castSucc with hf'def
    set x : R := f (Fin.last c) with hxdef
    have hreg'' : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f') := by
      rw [hf'def]; exact hreg'
    have hxreg'' : IsSMulRegular (R ⧸ Ideal.span (Set.range f')) x := by
      rw [hxdef]; exact hxreg
    have hIle : Ideal.span (Set.range f') ≤ Ideal.span (Set.range f) :=
      Ideal.span_mono (by rintro y ⟨i, rfl⟩; exact ⟨Fin.castSucc i, rfl⟩)
    have hxI : x ∈ Ideal.span (Set.range f) := by
      rw [hxdef]; exact Ideal.subset_span ⟨Fin.last c, rfl⟩
    -- Step A: replace `F` by `F - H` where `H` is a form of degree `n` with coefficients in `I`
    -- and `H(f) = F(f)`; then `(F - H)(f) = 0`.
    obtain ⟨H, hHhom, hHcoeff, hHeval⟩ := exists_homogeneous_coeff_mem_of_mem_pow f h
    set G : MvPolynomial (Fin (c + 1)) R := F - H with hGdef
    have hGhom : G.IsHomogeneous n := hF.sub hHhom
    have hGeval : MvPolynomial.eval f G = 0 := by
      rw [hGdef, map_sub, hHeval, sub_self]
    -- Step B: prove that all coefficients of `G` lie in `Ideal.span (Set.range f)`.
    have hGB : ∀ t, G.coeff t ∈ Ideal.span (Set.range f) := by
      intro t
      by_cases ht : G.coeff t = 0
      · rw [ht]; exact Submodule.zero_mem _
      · set g : Option (Fin c) → R := fun o => f (finSuccEquivLast.symm o) with hgdef
        set G' : MvPolynomial (Option (Fin c)) R :=
          MvPolynomial.rename finSuccEquivLast G with hG'def
        have hG'hom : G'.IsHomogeneous n := by
          rw [hG'def]
          exact MvPolynomial.IsHomogeneous.rename_isHomogeneous hGhom
        have hcomp : g ∘ finSuccEquivLast = f := by
          funext i
          rw [hgdef]
          simp
        have hGeval' : MvPolynomial.eval g G' = 0 := by
          rw [hG'def, MvPolynomial.eval_rename, hcomp, hGeval]
        set p : Polynomial (MvPolynomial (Fin c) R) :=
          MvPolynomial.optionEquivLeft R (Fin c) G' with hpdef
        have hp_hom : ((MvPolynomial.optionEquivLeft R (Fin c)).symm p).IsHomogeneous n := by
          rw [hpdef]
          simpa using hG'hom
        have hGf_hom : ∀ e ≤ n, ((fun e => p.coeff e) e).IsHomogeneous (n - e) := by
          intro e he
          exact MvPolynomial.IsHomogeneous.coeff_isHomogeneous_of_optionEquivLeft_symm
            hp_hom e (n - e) (by omega)
        -- the support of `p` is contained in `range (n+1)`
        have hsupp : p.support ⊆ Finset.range (n + 1) := by
          intro e he
          rw [Finset.mem_range]
          by_contra hcon
          push_neg at hcon
          have hpne : p.coeff e ≠ 0 := Polynomial.mem_support_iff.mp he
          obtain ⟨dd, hdd⟩ := MvPolynomial.exists_coeff_ne_zero hpne
          have hG'ne : G'.coeff (Finsupp.optionElim e dd) ≠ 0 := by
            rw [← MvPolynomial.optionEquivLeft_coeff_coeff R G' e dd, ← hpdef]
            exact hdd
          have hdeg : Finsupp.degree (Finsupp.optionElim e dd) = n := by
            by_contra hne
            exact hG'ne (MvPolynomial.IsHomogeneous.coeff_eq_zero hG'hom hne)
          have hle : e ≤ Finsupp.degree (Finsupp.optionElim e dd) := by
            calc e = (Finsupp.optionElim e dd) none := (Finsupp.optionElim_apply_none e dd).symm
              _ ≤ Finsupp.degree (Finsupp.optionElim e dd) := Finsupp.le_degree none _
          omega
        -- the relation `∑_{e ≤ n} p.coeff e (f') x^e = 0`
        have hrel : ∑ e ∈ Finset.range (n + 1), MvPolynomial.eval f' (p.coeff e) * x ^ e = 0 := by
          have hrel0 : Polynomial.eval₂ (MvPolynomial.eval f') x p = 0 := by
            have h1 := MvPolynomial.optionEquivLeft_elim_eval R (Fin c) f' x G'
            have hg_eq : (fun o : Option (Fin c) => o.elim x f') = g := by
              funext o
              cases o with
              | none => rw [hgdef]; simp [hxdef, finSuccEquivLast_symm_none]
              | some i => rw [hgdef]; simp [hf'def, finSuccEquivLast_symm_some]
            rw [hg_eq, hGeval', ← hpdef, ← Polynomial.eval₂_eq_eval_map] at h1
            exact h1.symm
          have h1 : Polynomial.eval₂ (MvPolynomial.eval f') x p
              = ∑ e ∈ p.support, MvPolynomial.eval f' (p.coeff e) * x ^ e := by
            rw [Polynomial.eval₂_eq_sum]
            rfl
          have h2 : ∑ e ∈ p.support, MvPolynomial.eval f' (p.coeff e) * x ^ e = 0 := by
            rw [← h1, hrel0]
          rw [← h2]
          exact (Finset.sum_subset hsupp (fun e _ hn => by
            rw [Polynomial.notMem_support_iff.mp hn]; simp)).symm
        -- apply the inner induction
        have hkey := inner_ind n f' x (Ideal.span (Set.range f)) hIle hxI hreg'' hxreg''
          (fun gg hreg => ih R gg hreg) n le_rfl (fun e => p.coeff e) hGf_hom hrel
        -- transport to `G.coeff t`
        set s' : Option (Fin c) →₀ ℕ := Finsupp.mapDomain finSuccEquivLast t with hs'def
        have hGs : G'.coeff s' = G.coeff t := by
          rw [hG'def, hs'def]
          exact MvPolynomial.coeff_rename_mapDomain finSuccEquivLast finSuccEquivLast.injective G t
        have hs'ne : G'.coeff s' ≠ 0 := by rw [hGs]; exact ht
        have hdeg : Finsupp.degree s' = n := by
          by_contra hne
          exact hs'ne (MvPolynomial.IsHomogeneous.coeff_eq_zero hG'hom hne)
        have hle : s' none ≤ n := by
          rw [← hdeg]
          exact Finsupp.le_degree none s'
        have hcoeff := hkey (s' none) hle s'.some
        rw [← hGs, ← MvPolynomial.optionEquivLeft_coeff_some_coeff_none R (Fin c) s' G', ← hpdef]
        exact hcoeff
    -- conclude
    have hFH : F = G + H := by rw [hGdef, sub_add_cancel]
    rw [hFH, MvPolynomial.coeff_add]
    exact Ideal.add_mem _ (hGB s) (hHcoeff s)

/-- **A regular sequence is quasi-regular** (Stacks 00LN, Lemma 10.69.2): a form of degree `n`
whose value at the sequence lies in the `(n+1)`-st power of the ideal generated by the sequence
has all its coefficients in that ideal. -/
theorem regularSequence_quasiRegular {R : Type*} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) {n : ℕ}
    (F : MvPolynomial (Fin c) R) (hF : F.IsHomogeneous n)
    (h : MvPolynomial.eval f F ∈ (Ideal.span (Set.range f)) ^ (n + 1)) :
    ∀ s, F.coeff s ∈ Ideal.span (Set.range f) :=
  aux c R f hreg n F hF h

end Work.DSNORM
