/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A flag basis adapted to the kernels of the `ψ j`

Let `L` be a field, `R` a Dedekind `L`-algebra and `ψ : Fin n → (R →ₐ[L] L)` a family of
`L`-algebra homomorphisms whose kernels are nonzero.  Writing `m j = RingHom.ker (ψ j)` and
`J = ∏ j, m j`, the quotient `R ⧸ J` is an `n`-dimensional `L`-vector space, and it carries a
*flag*: the chain of ideals `A k = m 0 * m 1 * ... * m (k-1)` (for `k = 0, ..., n`) descends to a
complete flag of `R ⧸ J` whose `j`-th successive quotient is one-dimensional with the action of
`R` on it given by `ψ j`.

`exists_flagBasis` produces a basis `u` of `R ⧸ J` that is adapted to this flag: for every
`j : Fin n` and `b : R`, the `j`-th basis vector satisfies

`mk b * u j - ψ j b • u j ∈ span {u k | j < k}`,

i.e. the matrix of multiplication by `b` in the basis `u` is upper triangular with diagonal
entries `ψ j b`.  This is the algebraic input for the computation of the norm functional on the
tensor power of a finite flat algebra (`Work.SymQuot.NormPoint.normVal_eq_evalT`).
-/
import Mathlib
import Submission.Work.SymQuot.NormPoint.exists_gen_mod_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

universe u

namespace Work.SymQuot.NormPoint


/-! ### The chain `A k = m 0 * ... * m (k-1)` -/

section Chain

variable {R : Type u} [CommRing R] {n : ℕ}

/-- `prodChain m k` is the product `m 0 * m 1 * ... * m (k-1)` of the first `k` ideals,
padded with `⊤` for `k ≥ n`. -/
def prodChain (m : Fin n → Ideal R) (k : ℕ) : Ideal R :=
  ∏ i ∈ Finset.range k, if h : i < n then m ⟨i, h⟩ else ⊤

@[simp] theorem prodChain_zero (m : Fin n → Ideal R) : prodChain m 0 = ⊤ := by
  simp [prodChain]

theorem prodChain_succ (m : Fin n → Ideal R) (k : ℕ) :
    prodChain m (k + 1) = prodChain m k * (if h : k < n then m ⟨k, h⟩ else ⊤) := by
  rw [prodChain, prodChain, Finset.prod_range_succ]

theorem prodChain_succ_of_lt (m : Fin n → Ideal R) {k : ℕ} (hk : k < n) :
    prodChain m (k + 1) = prodChain m k * m ⟨k, hk⟩ := by
  rw [prodChain_succ, dite_eq_left hk]

theorem prodChain_n (m : Fin n → Ideal R) : prodChain m n = ∏ j : Fin n, m j := by
  rw [prodChain, ← Fin.prod_univ_eq_prod_range
    (fun i => if h : i < n then m ⟨i, h⟩ else (⊤ : Ideal R)) n]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [dite_eq_left i.isLt]

theorem prodChain_anti (m : Fin n → Ideal R) : ∀ k, prodChain m (k + 1) ≤ prodChain m k := by
  intro k
  rw [prodChain_succ]
  exact le_trans (mul_le_mul_right le_top (prodChain m k)) (le_of_eq (Ideal.mul_top _))

theorem prodChain_antitone (m : Fin n → Ideal R) : Antitone (prodChain m) :=
  antitone_nat_of_succ_le (prodChain_anti m)

theorem prodChain_ne_bot [NoZeroDivisors R] [Nontrivial R] (m : Fin n → Ideal R)
    (hm : ∀ j, m j ≠ ⊥) : ∀ k, k ≤ n → prodChain m k ≠ ⊥ := by
  intro k
  induction k with
  | zero => intro _; rw [prodChain_zero]; exact top_ne_bot
  | succ k ih =>
    intro hk
    rw [prodChain_succ_of_lt m (by omega)]
    exact fun h => (Ideal.mul_eq_bot.mp h).elim (ih (by omega)) (hm _)

end Chain

/-! ### Basic facts about the quotient map -/

section Quot

variable {L : Type u} [Field L] {R : Type u} [CommRing R] [Algebra L R] {J : Ideal R}

/-- The quotient map is `L`-linear. -/
lemma mk_smul_eq (c : L) (a : R) :
    Ideal.Quotient.mk J (c • a) = c • Ideal.Quotient.mk J a := by
  simp only [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply L R (R ⧸ J),
    Ideal.Quotient.algebraMap_eq J]

/-- The image of an ideal `B ⊇ J` in `R ⧸ J` is already an `L`-submodule, so that
`mk x` lies in its span exactly when `x ∈ B`. -/
lemma mk_mem_span_image_iff (B : Ideal R) (hJB : J ≤ B) (x : R) :
    Ideal.Quotient.mk J x ∈ Submodule.span L ((Ideal.Quotient.mk J) '' (B : Set R)) ↔ x ∈ B := by
  constructor
  · intro hx
    let T : Submodule L (R ⧸ J) :=
      { carrier := (Ideal.Quotient.mk J) '' (B : Set R)
        zero_mem' := ⟨0, B.zero_mem, map_zero _⟩
        add_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, B.add_mem ha hb, by rw [map_add]⟩
        smul_mem' := by
          rintro c _ ⟨a, ha, rfl⟩
          exact ⟨c • a, by rw [Algebra.smul_def]; exact Ideal.mul_mem_left B _ ha,
            mk_smul_eq c a⟩ }
    have hT : Submodule.span L ((Ideal.Quotient.mk J) '' (B : Set R)) = T :=
      Submodule.span_eq T
    rw [hT] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have h1 : (Ideal.Quotient.mk J) (a - x) = 0 := by rw [map_sub, hax, sub_self]
    have h2 : a - x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp h1
    have h3 : x - a ∈ J := by simpa using neg_mem h2
    have h4 : x = a + (x - a) := by ring
    rw [h4]
    exact B.add_mem ha (hJB h3)
  · intro hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩

end Quot

/-! ### Flag bases from a filtration -/

section Filtration

variable {L : Type u} [Field L] {V : Type u} [AddCommGroup V] [Module L V]

/-- If `u : Fin n → V` is compatible with a decreasing filtration `W` whose successive
quotients are spanned by the `u j`, then `u` is linearly independent. -/
theorem flag_independent {n : ℕ} {W : ℕ → Submodule L V} {u : Fin n → V}
    (hmono : ∀ k, W (k + 1) ≤ W k) (hu_mem : ∀ j : Fin n, u j ∈ W (j : ℕ))
    (hu_not : ∀ j : Fin n, u j ∉ W ((j : ℕ) + 1)) : LinearIndependent L u := by
  classical
  have hanti : Antitone W := antitone_nat_of_succ_le hmono
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra h
  simp only [not_forall] at h
  obtain ⟨i₀, hi₀⟩ := h
  set s : Finset (Fin n) := Finset.univ.filter (fun k => g k ≠ 0) with hs
  have hsne : s.Nonempty := ⟨i₀, by rw [hs]; simp [hi₀]⟩
  set j := s.min' hsne with hj
  have hjm : j ∈ s := Finset.min'_mem s hsne
  have hgj : g j ≠ 0 := by rw [hs] at hjm; simpa using hjm
  have hmin : ∀ k ∈ s, j ≤ k := fun k hk => Finset.min'_le s k hk
  have hsum : ∑ k ∈ s, g k • u k = 0 := by
    have h1 := Finset.sum_filter_of_ne (s := Finset.univ)
      (f := fun k : Fin n => g k • u k) (p := fun k => g k ≠ 0)
      (fun x _ hx => fun hgx => hx (by simp [hgx]))
    rw [hs, h1]
    simpa using hg
  have hsplit : ∑ k ∈ s.erase j, g k • u k + g j • u j = 0 := by
    rw [Finset.sum_erase_add s (fun k => g k • u k) hjm]
    exact hsum
  have hT : ∑ k ∈ s.erase j, g k • u k ∈ W ((j : ℕ) + 1) := by
    apply Submodule.sum_mem
    intro k hk
    have hkm : k ∈ s := Finset.mem_of_mem_erase hk
    have hkne : k ≠ j := Finset.ne_of_mem_erase hk
    have hjk : j < k := lt_of_le_of_ne (hmin k hkm) (Ne.symm hkne)
    have hjk' : (j : ℕ) + 1 ≤ (k : ℕ) := by
      have := hjk; simp only [Fin.lt_def] at this; omega
    exact Submodule.smul_mem _ _ (hanti hjk' (hu_mem k))
  have hgjuj : g j • u j ∈ W ((j : ℕ) + 1) := by
    have := eq_neg_of_add_eq_zero_right hsplit
    rw [this]
    exact Submodule.neg_mem _ hT
  have huj : u j ∈ W ((j : ℕ) + 1) := by
    have h2 : (g j)⁻¹ • (g j • u j) ∈ W ((j : ℕ) + 1) := Submodule.smul_mem _ _ hgjuj
    rwa [smul_smul, inv_mul_cancel₀ hgj, one_smul] at h2
  exact hu_not j huj

/-- Under the same hypotheses, the filtration is spanned by the tails of `u`. -/
theorem flag_tail {n : ℕ} {W : ℕ → Submodule L V} {u : Fin n → V} (hWn : W n = ⊥)
    (hstep : ∀ (k : ℕ) (hk : k < n),
      W k ≤ W (k + 1) ⊔ Submodule.span L {u ⟨k, hk⟩}) :
    ∀ j : Fin n, W ((j : ℕ) + 1) ≤ Submodule.span L (u '' {k : Fin n | j < k}) := by
  have hset : ∀ j : Fin n, {k : Fin n | (j : ℕ) + 1 ≤ (k : ℕ)} = {k : Fin n | j < k} := by
    intro j
    ext k
    simp only [Set.mem_ofPred_eq, Fin.lt_def]
    omega
  suffices hkey : ∀ d k, n - k = d → k ≤ n →
      W k ≤ Submodule.span L (u '' {j : Fin n | k ≤ (j : ℕ)}) by
    intro j
    have h := hkey (n - ((j : ℕ) + 1)) ((j : ℕ) + 1) rfl (by omega)
    rwa [hset j] at h
  intro d
  induction d with
  | zero =>
    intro k hkd hkn
    have : k = n := by omega
    subst this
    rw [hWn]; exact bot_le
  | succ d ih =>
    intro k hkd hkn
    have hk : k < n := by omega
    have hnext : n - (k + 1) = d := by omega
    have hrec : W (k + 1) ≤ Submodule.span L (u '' {j : Fin n | k + 1 ≤ (j : ℕ)}) :=
      ih (k + 1) hnext (by omega)
    have hA : u '' {j : Fin n | k + 1 ≤ (j : ℕ)} ⊆ u '' {j : Fin n | k ≤ (j : ℕ)} := by
      rintro x ⟨j, hj, rfl⟩
      exact ⟨j, by simp only [Set.mem_ofPred_eq] at hj ⊢; omega, rfl⟩
    have huk : u ⟨k, hk⟩ ∈ u '' {j : Fin n | k ≤ (j : ℕ)} := ⟨⟨k, hk⟩, by simp, rfl⟩
    refine le_trans (hstep k hk) (sup_le (le_trans hrec (Submodule.span_mono hA)) ?_)
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (Submodule.subset_span huk))

/-- Under the same hypotheses, `u` spans. -/
theorem flag_span {n : ℕ} {W : ℕ → Submodule L V} {u : Fin n → V} (hW0 : W 0 = ⊤)
    (hWn : W n = ⊥) (hstep : ∀ (k : ℕ) (hk : k < n),
      W k ≤ W (k + 1) ⊔ Submodule.span L {u ⟨k, hk⟩}) :
    ⊤ ≤ Submodule.span L (Set.range u) := by
  have key : ∀ k, k ≤ n → W 0 ≤ Submodule.span L (u '' {j : Fin n | (j : ℕ) < k}) ⊔ W k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk1
      have hk : k < n := by omega
      have ih' := ih (by omega)
      have hA : u '' {j : Fin n | (j : ℕ) < k} ⊆ u '' {j : Fin n | (j : ℕ) < k + 1} := by
        rintro x ⟨j, hj, rfl⟩
        exact ⟨j, by simp only [Set.mem_ofPred_eq] at hj ⊢; omega, rfl⟩
      have huk : u ⟨k, hk⟩ ∈ u '' {j : Fin n | (j : ℕ) < k + 1} := ⟨⟨k, hk⟩, by simp, rfl⟩
      refine le_trans ih' (sup_le ?_ ?_)
      · exact le_trans (Submodule.span_mono hA) le_sup_left
      · refine le_trans (hstep k hk) (sup_le le_sup_right ?_)
        exact le_trans (Submodule.span_le.mpr
          (Set.singleton_subset_iff.mpr (Submodule.subset_span huk))) le_sup_left
  have hset : u '' {j : Fin n | (j : ℕ) < n} = Set.range u := by
    rw [show {j : Fin n | (j : ℕ) < n} = Set.univ from
      Set.eq_univ_of_forall (fun j => j.isLt), Set.image_univ]
  have hthis := key n le_rfl
  rw [hset, hW0, hWn] at hthis
  simpa using hthis

end Filtration

/-! ### The main theorem -/

theorem exists_flagBasis {L R : Type u} [Field L] [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [Algebra L R] {n : ℕ} (ψ : Fin n → R →ₐ[L] L)
    (hψ : ∀ j, RingHom.ker (ψ j) ≠ ⊥) :
    ∃ u : Module.Basis (Fin n) L (R ⧸ ∏ j, RingHom.ker (ψ j)),
      ∀ j (b : R), Ideal.Quotient.mk _ b * u j - ψ j b • u j ∈
        Submodule.span L (u '' {k | j < k}) := by
  classical
  set m : Fin n → Ideal R := fun j => RingHom.ker (ψ j)
  set J : Ideal R := ∏ j : Fin n, m j
  have hm_ne : ∀ j, m j ≠ ⊥ := fun j => hψ j
  have key : ∀ j : Fin n, ∃ u : R, u ∈ prodChain m (j:ℕ) ∧ u ∉ prodChain m ((j:ℕ)+1) ∧
      (∀ a ∈ prodChain m (j:ℕ), ∃ c : L, a - c • u ∈ prodChain m ((j:ℕ)+1)) := by
    intro j
    have hlt : (j : ℕ) < n := j.isLt
    have hne : prodChain m (j : ℕ) ≠ ⊥ := prodChain_ne_bot m hm_ne (j:ℕ) j.isLt.le
    obtain ⟨u, hu, hnu, hgen⟩ := exists_gen_mod_mul (I := prodChain m (j:ℕ)) hne (ψ j)
    refine ⟨u, hu, ?_, ?_⟩
    · intro h
      rw [prodChain_succ_of_lt m hlt] at h
      exact hnu h
    · intro a ha
      obtain ⟨c, hc⟩ := hgen a ha
      refine ⟨c, ?_⟩
      rw [prodChain_succ_of_lt m hlt]
      exact hc
  let u : Fin n → R := fun j => (key j).choose
  have hu_mem : ∀ j : Fin n, u j ∈ prodChain m (j:ℕ) := fun j => (key j).choose_spec.1
  have hu_not : ∀ j : Fin n, u j ∉ prodChain m ((j:ℕ)+1) := fun j => (key j).choose_spec.2.1
  have hu_gen : ∀ (j : Fin n) (a : R), a ∈ prodChain m (j:ℕ) →
      ∃ c : L, a - c • u j ∈ prodChain m ((j:ℕ)+1) := fun j => (key j).choose_spec.2.2
  set V := R ⧸ J with hV
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  let ubar : Fin n → V := fun j => Ideal.Quotient.mk J (u j)
  let Wt : ℕ → Submodule L V := fun k =>
    Submodule.span L ((Ideal.Quotient.mk J) '' (prodChain m k : Set R))
  have hWt0 : Wt 0 = ⊤ := by
    have himg : (Ideal.Quotient.mk J) '' ((⊤ : Ideal R) : Set R) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      obtain ⟨r, rfl⟩ := hsurj x
      exact ⟨r, by simp, rfl⟩
    show Submodule.span L ((Ideal.Quotient.mk J) '' (prodChain m 0 : Set R)) = ⊤
    rw [prodChain_zero, himg, Submodule.span_univ]
  have hWtn : Wt n = ⊥ := by
    show Submodule.span L ((Ideal.Quotient.mk J) '' (prodChain m n : Set R)) = ⊥
    rw [eq_bot_iff, Submodule.span_le]
    rintro x ⟨a, ha, rfl⟩
    rw [prodChain_n] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hWtanti : ∀ k, Wt (k+1) ≤ Wt k := by
    intro k
    exact Submodule.span_mono (Set.image_mono (fun _ hx => prodChain_anti m k hx))
  have hJB : ∀ k, k ≤ n → J ≤ prodChain m k := by
    intro k hk
    have h := prodChain_antitone m hk
    rwa [prodChain_n] at h
  have hu_mem' : ∀ j : Fin n, ubar j ∈ Wt (j:ℕ) := by
    intro j
    exact Submodule.subset_span ⟨u j, hu_mem j, rfl⟩
  have hu_not' : ∀ j : Fin n, ubar j ∉ Wt ((j:ℕ)+1) := by
    intro j hmem
    exact hu_not j
      ((mk_mem_span_image_iff (prodChain m ((j:ℕ)+1)) (hJB _ (by omega)) (u j)).mp hmem)
  have hWtstep : ∀ (k : ℕ) (hk : k < n),
      Wt k ≤ Wt (k+1) ⊔ Submodule.span L {ubar ⟨k, hk⟩} := by
    intro k hk
    show Submodule.span L ((Ideal.Quotient.mk J) '' (prodChain m k : Set R)) ≤ _
    rw [Submodule.span_le]
    rintro x ⟨a, ha, rfl⟩
    obtain ⟨c, hc⟩ := hu_gen ⟨k, hk⟩ a ha
    have h1 : Ideal.Quotient.mk J a
        = Ideal.Quotient.mk J (a - c • u ⟨k, hk⟩) + c • ubar ⟨k, hk⟩ := by
      show Ideal.Quotient.mk J a
        = Ideal.Quotient.mk J (a - c • u ⟨k, hk⟩) + c • Ideal.Quotient.mk J (u ⟨k, hk⟩)
      rw [← mk_smul_eq (J := J) c (u ⟨k,hk⟩), ← map_add, sub_add_cancel]
    refine Submodule.mem_sup.mpr ⟨Ideal.Quotient.mk J (a - c • u ⟨k, hk⟩),
      Submodule.subset_span ⟨_, hc, rfl⟩, c • ubar ⟨k, hk⟩,
      Submodule.smul_mem _ c (Submodule.subset_span (by simp)), h1.symm⟩
  have hli : LinearIndependent L ubar := flag_independent hWtanti hu_mem' hu_not'
  have hsp : ⊤ ≤ Submodule.span L (Set.range ubar) := flag_span hWt0 hWtn hWtstep
  have htail : ∀ j : Fin n, Wt ((j:ℕ)+1) ≤ Submodule.span L (ubar '' {k : Fin n | j < k}) :=
    flag_tail hWtn hWtstep
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  have hbb : ∀ i : Fin n, (Module.Basis.mk hli hsp) i = ubar i :=
    fun i => Module.Basis.mk_apply hli hsp i
  intro j b
  simp only [hbb]
  show Ideal.Quotient.mk J b * ubar j - ψ j b • ubar j ∈
    Submodule.span L (ubar '' {k : Fin n | j < k})
  have hker : b - algebraMap L R (ψ j b) ∈ m j := by
    show b - algebraMap L R (ψ j b) ∈ RingHom.ker (ψ j)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  have hc : (b - algebraMap L R (ψ j b)) * u j ∈ prodChain m ((j:ℕ)+1) := by
    have h1 : (b - algebraMap L R (ψ j b)) * u j ∈ m j * prodChain m (j:ℕ) :=
      Ideal.mul_mem_mul hker (hu_mem j)
    rwa [mul_comm (m j) (prodChain m (j:ℕ)), ← prodChain_succ_of_lt m j.isLt] at h1
  have hfin : Ideal.Quotient.mk J b * ubar j - ψ j b • ubar j
      = Ideal.Quotient.mk J ((b - algebraMap L R (ψ j b)) * u j) := by
    show Ideal.Quotient.mk J b * Ideal.Quotient.mk J (u j)
        - ψ j b • Ideal.Quotient.mk J (u j) = _
    rw [← map_mul, ← mk_smul_eq (J := J) (ψ j b) (u j), Algebra.smul_def, ← map_sub]
    congr 1
    ring
  rw [hfin]
  exact (htail j) (Submodule.subset_span ⟨_, hc, rfl⟩)

end Work.SymQuot.NormPoint
