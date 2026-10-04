import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.antisymN_aux
import Submission.Work.Diff.STE.flat.periodic_shift
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Derived bounds for the DeTurck nonlinearity of the flat Cauchy problem

The nonlinearity `Φ` of the flat DeTurck system is, on the nondegenerate locus
`{det (reMat A) ≠ 0}`, of the shape `Φ (x,(A,L,B)) = secOpFlat A B + N (x,(A,L))`, with `N` smooth
and `1`-periodic in `x` (`Work.Diff.STE.Flat.IsDeTurckNonlin`).  This file proves
`Work.Diff.STE.flat.nonlin_deriv_bound`: there is a *single* constant `K ≥ 0` bounding *all*
iterated Fréchet derivatives `‖D^j N (x,A,L)‖`, `j ≤ s+1`, at the points `(A,L)` that arise as the
spatial `(value, first jet)` of a coefficient family `c : (Fin n → ℤ) → MatC n` which is

* supported in the box `box n N`,
* has full energy `ENormSqFull s (seriesFunM c) ≤ Bs²`, and
* is uniformly `lam`-elliptic as a quadratic form, `lam > 0`,

with `n + 5 ≤ s`.

## Proof

* The Sobolev level is high enough (`n + 5 ≤ s`) that the sup bounds of
  `Work.Diff.STE.flat.jet_sup_le` apply to the value and the first jet: there is `KA ≥ 0` —
  *uniform in `N` and in `c`*, `jet_entry_uniform` (this uniformity is not in `jet_sup_le`, whose
  constant is produced inside the quantifiers; the proof of `jet_sup_le` shows the constant only
  depends on `n`, `s`, `m`) — with `‖seriesFunM c x i j‖ ≤ KA` and
  `‖∂_a (seriesFunM c · i j) x‖ ≤ KA` for all `x`, `a`, `i`, `j`.
* Hence every reachable `(A,L)` lies in the admissible set `posSet KA lam`
  (`antisymN_aux`/`posSet_props`), which is compact and contained in the open domain
  `domN = univ ×ˢ {det (reMat ·) ≠ 0}` of `N`.
* `cubeN ×ˢ posSet KA lam` is therefore a compact subset of `domN`, so the smooth function `N` has
  all its derivatives up to order `s+1` uniformly bounded on it by some `K ≥ 0`
  (`compact_iteratedFDeriv_bound`).
* A point `(x, A, L)` with an arbitrary `x` is moved into the fundamental domain by the integer
  translation `x ↦ x - ⌊x⌋`: `periodic_shift` shows that the iterated derivatives of a function
  periodic in the Euclidean variable are invariant under integer translations.

This is the "derivative bound" input of the flat short-time existence argument: it upgrades the
sup bounds on the nonlinearity along the Galerkin flow to bounds on the derivatives with respect to
the (value, first jet) variables, which is what the Lipschitz/Faà-di-Bruno estimates of the
Galerkin bootstrap (`nonlin_bound_short`, `energy_apriori`) consume.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

variable {n s : ℕ}

/-! ## The uniform-in-`c` sup bound for the spatial jet -/

/-- **Sup bounds for derivatives up to order `s - sob n`, uniform in the coefficient family.**
This is `jet_sup_le` with the constant extracted outside the quantifiers over `N` and `c` (the
proof of `jet_sup_le` shows that the constant only depends on `n`, `s` and `m`). -/
private lemma jet_sup_le_uniform (m : ℕ) (hm : m + sob n ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ∀ (l : Fin m → Fin n) (i j : Fin n) (x : Fin n → ℝ),
        ‖pdVec m l (fun y => seriesFunM c y i j) x‖
          ≤ C * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := by
  obtain ⟨C0, hC0, h0⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (sob n)
    (by simpa using n_lt_two_sob n)
  obtain ⟨C2, hC2, h2⟩ := Work.Diff.STE.CSq_le_ENormSq_seriesFun (ι := Fin n) s
  refine ⟨C0 * (2 * Real.pi) ^ m * Real.sqrt C2, by positivity, ?_⟩
  intro N c hc l i j x
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext y; rw [seriesFunM_apply]
  rw [hfun]
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hsumm : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ M *
      ‖(fun k : Fin n → ℤ => c k i j) k‖) := hmom
  have hpd : Work.Diff.STE.pdVec m l (Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c k i j)) x
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l)
          (fun k => c k i j)) x := by
    rw [Work.Diff.STE.pdVec]
    exact Work.Diff.STE.pdList_seriesFun (List.ofFn l) (fun k => c k i j) hmom x
  rw [hpd]
  have hstep := h0 (Work.Diff.STE.dmulV (List.ofFn l) (fun k => c k i j))
    (Work.Diff.STE.summable_wt_pow_mul_norm_sq _
      (fun M => Work.Diff.STE.summable_dmulV _ _ hmom M) (sob n)) x
  have hCSq : Work.Diff.STE.CSq (sob n) (Work.Diff.STE.dmulV (List.ofFn l)
      (fun k => c k i j))
      ≤ ((2 * Real.pi) ^ 2) ^ m * Work.Diff.STE.CSq (sob n + m) (fun k => c k i j) := by
    have h := CSq_dmulV_le (sob n) (List.ofFn l) (fun k => c k i j) hmom
    simpa [List.length_ofFn] using h
  have hlev : sob n + m ≤ s := by omega
  have hmono : Work.Diff.STE.CSq (sob n + m) (fun k : Fin n → ℤ => c k i j)
      ≤ Work.Diff.STE.CSq s (fun k : Fin n → ℤ => c k i j) := by
    rw [Work.Diff.STE.CSq, Work.Diff.STE.CSq]
    refine Summable.tsum_le_tsum (fun k => ?_)
      (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ hsumm (sob n + m))
      (Work.Diff.STE.summable_wt_pow_mul_norm_sq _ hsumm s)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (Work.Diff.STE.wt_one_le k) hlev) (sq_nonneg _)
  have h4 : Work.Diff.STE.CSq s (fun k : Fin n → ℤ => c k i j)
      ≤ C2 * ENormSqFull s (seriesFunM c) := by
    have h := h2 (fun k => c k i j) hsumm
    have hEs : Work.Diff.STE.ENormSq s (Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM s (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := s) (seriesFunM c) i j
      rwa [hfun] at hh
    have hE0 : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
      rwa [hfun] at hh
    refine h.trans ?_
    rw [ENormSqFull]
    exact mul_le_mul_of_nonneg_left (add_le_add hEs hE0) hC2
  calc ‖Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) (fun k => c k i j)) x‖
      ≤ C0 * Real.sqrt (Work.Diff.STE.CSq (sob n) (Work.Diff.STE.dmulV (List.ofFn l)
          (fun k => c k i j))) := hstep
    _ ≤ C0 * Real.sqrt (((2 * Real.pi) ^ 2) ^ m
          * Work.Diff.STE.CSq (sob n + m) (fun k => c k i j)) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCSq) hC0
    _ = C0 * ((2 * Real.pi) ^ m
          * Real.sqrt (Work.Diff.STE.CSq (sob n + m) (fun k => c k i j))) := by
        have hsq : ((2 * Real.pi) ^ 2) ^ m = ((2 * Real.pi) ^ m) ^ 2 := by
          rw [← pow_mul]; ring_nf
        rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ C0 * ((2 * Real.pi) ^ m * Real.sqrt (C2 * ENormSqFull s (seriesFunM c))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
        exact hmono.trans h4
    _ = C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2
          * Real.sqrt (ENormSqFull s (seriesFunM c)))) := by
        rw [Real.sqrt_mul hC2]
    _ ≤ C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg C2)
    _ = C0 * (2 * Real.pi) ^ m * Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := by ring

/-- **Entry bounds for the spatial `2`-jet of `seriesFunM c`**, uniform in the box order `N` and in
the coefficient family `c`, derived from the energy bound `ENormSqFull s ≤ Bs ^ 2`. -/
private lemma jet_entry_uniform (hs : n + 5 ≤ s) {Bs : ℝ} (hBs : 0 ≤ Bs) :
    ∃ KA : ℝ, 0 ≤ KA ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (i j : Fin n), ‖seriesFunM c x i j‖ ≤ KA) ∧
      (∀ (x : Fin n → ℝ) (a i j : Fin n),
        ‖Work.Diff.STE.pd a (fun y => seriesFunM c y i j) x‖ ≤ KA) := by
  have hsob0 : 0 + sob n ≤ s := by
    have : n / 2 ≤ n := Nat.div_le_self n 2; simp only [sob]; omega
  have hsob1 : 1 + sob n ≤ s := by
    have : n / 2 ≤ n := Nat.div_le_self n 2; simp only [sob]; omega
  obtain ⟨C0, hC00, h0⟩ := jet_sup_le_uniform (n := n) (s := s) 0 hsob0
  obtain ⟨C1, hC10, h1⟩ := jet_sup_le_uniform (n := n) (s := s) 1 hsob1
  refine ⟨max C0 C1 * (1 + Bs), ?_, ?_⟩
  · have h1' : (0 : ℝ) ≤ max C0 C1 := le_max_of_le_left hC00
    have h2' : (0 : ℝ) ≤ 1 + Bs := by linarith
    positivity
  intro N c hc hE
  have hsqrt : Real.sqrt (ENormSqFull s (seriesFunM c)) ≤ Bs := by
    have h := Real.sqrt_le_sqrt hE
    rwa [Real.sqrt_sq hBs] at h
  have hb0 := h0 N c hc
  have hb1 := h1 N c hc
  refine ⟨fun x i j => ?_, fun x a i j => ?_⟩
  · have h := hb0 (fun i : Fin 0 => i.elim0) i j x
    calc ‖seriesFunM c x i j‖
        = ‖pdVec 0 (fun i : Fin 0 => i.elim0) (fun y => seriesFunM c y i j) x‖ := by
          simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
      _ ≤ C0 * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := h
      _ ≤ C0 * (1 + Bs) := by
          refine mul_le_mul_of_nonneg_left (by linarith) hC00
      _ ≤ max C0 C1 * (1 + Bs) := by
          refine mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · have h := hb1 (fun _ : Fin 1 => a) i j x
    calc ‖Work.Diff.STE.pd a (fun y => seriesFunM c y i j) x‖
        = ‖pdVec 1 (fun _ : Fin 1 => a) (fun y => seriesFunM c y i j) x‖ := by
          simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
      _ ≤ C1 * (1 + Real.sqrt (ENormSqFull s (seriesFunM c))) := h
      _ ≤ C1 * (1 + Bs) := by
          refine mul_le_mul_of_nonneg_left (by linarith) hC10
      _ ≤ max C0 C1 * (1 + Bs) := by
          refine mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

/-! ## The domain of the nonlinearity is open -/

private lemma continuous_det_reMat :
    Continuous (fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det) := by
  refine Continuous.matrix_det ?_
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  exact Complex.continuous_re.comp
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))

private lemma isOpen_domN : IsOpen (domN (n := n)) := by
  have hU : IsOpen (detNeZeroSet (n := n)) := by
    have hcl : IsClosed {w : MatC n × (Fin n → MatC n) | (reMat w.1).det = 0} :=
      isClosed_eq continuous_det_reMat continuous_const
    have hsub : detNeZeroSet (n := n) =
        {w : MatC n × (Fin n → MatC n) | (reMat w.1).det = 0}ᶜ := by
      ext w; simp [detNeZeroSet, Set.mem_compl_iff]
    rw [hsub]; exact hcl.isOpen_compl
  exact isOpen_univ.prod hU

theorem nonlin_deriv_bound {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ (K : ℝ) (Nfun : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n ×
        (Fin n → Work.Diff.STE.Flat.MatC n)) → Work.Diff.STE.Flat.MatC n),
      0 ≤ K ∧
      ContDiffOn ℝ (⊤ : ℕ∞) Nfun (Set.univ ×ˢ
        {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n)
          | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}) ∧
      (∀ w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n),
        Work.Diff.STE.Periodic1 (fun x : Fin n → ℝ => Nfun (x, w))) ∧
      (∀ (x : Fin n → ℝ) (A : Work.Diff.STE.Flat.MatC n)
        (L : Fin n → Work.Diff.STE.Flat.MatC n)
        (B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n),
        (Work.Diff.STE.Flat.reMat A).det ≠ 0 →
          Φ (x, (A, L, B)) = Work.Diff.STE.Flat.secOpFlat A B + Nfun (x, (A, L))) ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k : Fin n → ℤ, k ∉ Work.Diff.STE.Flat.box n N → c k = 0) →
        Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        ∀ (j : ℕ) (hj : j ≤ s + 1) (x : Fin n → ℝ),
          ‖iteratedFDeriv ℝ j Nfun
            (x, Work.Diff.STE.Flat.seriesFunM c x,
              fun a i j' => Work.Diff.STE.pd a (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)‖
            ≤ K := by
  obtain ⟨-, Nfn, hNsm, hNshape, hNper⟩ := hshape
  obtain ⟨KA, hKA0, hKA⟩ := jet_entry_uniform (n := n) (s := s) hs hBs
  have hUopen : IsOpen (domN (n := n)) := isOpen_domN
  have hCcomp : IsCompact (cubeN (n := n) ×ˢ posSet (n := n) KA lam) :=
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).prod (posSet_isCompact KA lam hKA0)
  have hCsub : cubeN (n := n) ×ˢ posSet (n := n) KA lam ⊆ domN (n := n) :=
    fun p hp => ⟨trivial, posSet_subset_detNeZero KA lam hlam hp.2⟩
  obtain ⟨K, hK0, hKb⟩ :=
    compact_iteratedFDeriv_bound Nfn hUopen hNsm hCcomp hCsub (s + 1)
  refine ⟨K, Nfn, hK0, hNsm, hNper, hNshape, ?_⟩
  intro N c hc hE hell j hj x
  have hentry := hKA N c hc hE
  have hw : (seriesFunM c x, fun a i j' => Work.Diff.STE.pd a
        (fun y => seriesFunM c y i j') x) ∈ posSet (n := n) KA lam := by
    refine mem_posSet.mpr ⟨hentry.1 x, fun a i j' => hentry.2 x a i j', ?_⟩
    intro ξ
    have h := hell x ξ
    simpa [quadForm] using h
  have hxcube : (fun i : Fin n => x i - ((⌊x i⌋ : ℤ) : ℝ)) ∈ cubeN (n := n) := by
    intro i _
    exact ⟨by have := Int.floor_le (x i); linarith,
           by have := Int.lt_floor_add_one (x i); linarith⟩
  have hxeq : (fun i : Fin n => x i - ((⌊x i⌋ : ℤ) : ℝ)) +
      (fun i : Fin n => (((fun j : Fin n => ⌊x j⌋) i : ℤ) : ℝ)) = x := by
    funext i; simp
  have hshift := periodic_shift Nfn hNper (fun i : Fin n => ⌊x i⌋)
    (seriesFunM c x, fun a i j' => Work.Diff.STE.pd a (fun y => seriesFunM c y i j') x) j
    (fun i : Fin n => x i - ((⌊x i⌋ : ℤ) : ℝ))
  rw [hxeq] at hshift
  rw [hshift]
  exact hKb _ ⟨hxcube, hw⟩ j hj

end

end Work.Diff.STE.flat
