import Mathlib
import Submission.Work.Higman.H8.frob_orbit
import Submission.Work.Higman.H8.frob_component
import Submission.Work.Higman.exists_singer_iso
import Submission.Work.Higman.QuadAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
open Polynomial

namespace Work.Higman.H8

namespace FSB

variable {n : ℕ}

abbrev EndF (n : ℕ) := GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n

/-- The `k`-th Frobenius monomial `x ↦ c * x ^ (2 ^ k)`, an `𝔽₂`-linear map. -/
noncomputable def frobComp (k : ℕ) (c : GaloisField 2 n) :
    GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n where
  toFun x := c * x ^ (2 ^ k)
  map_add' x y := by rw [add_pow_char_pow, mul_add]
  map_smul' a x := by
    rcases zmod2_eq_zero_or_one a with rfl | rfl
    · simp [zero_pow (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0))]
    · simp

@[simp] lemma frobComp_apply (k : ℕ) (c x : GaloisField 2 n) :
    frobComp k c x = c * x ^ (2 ^ k) := rfl

@[simp] lemma frobComp_zero (k : ℕ) : frobComp k (0 : GaloisField 2 n) = 0 := by
  ext x; simp

noncomputable def frobCompLM (k : ℕ) :
    GaloisField 2 n →ₗ[ZMod 2] (EndF n) where
  toFun c := frobComp k c
  map_add' c c' := by ext x; simp [add_mul]
  map_smul' a c := by
    ext x
    rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

noncomputable def Mk (k : ℕ) : Submodule (ZMod 2) (EndF n) :=
  LinearMap.range (frobCompLM (n := n) k)

lemma mem_Mk {k : ℕ} {f : EndF n} :
    f ∈ Mk k ↔ ∃ c, frobComp k c = f := LinearMap.mem_range

noncomputable def singAct (ν : (GaloisField 2 n)ˣ) : EndF n →ₗ[ZMod 2] EndF n where
  toFun f := conjAction ν f
  map_add' f g := by
    ext x; simp only [conjAction_apply, LinearMap.add_apply]; ring
  map_smul' a f := by
    ext x
    simp only [conjAction_apply, LinearMap.smul_apply, RingHom.id_apply]
    rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

@[simp] lemma singAct_apply (ν : (GaloisField 2 n)ˣ) (f : EndF n) :
    singAct ν f = conjAction ν f := rfl

lemma singAct_frobComp (ν : (GaloisField 2 n)ˣ) (k : ℕ) (c : GaloisField 2 n) :
    singAct ν (frobComp k c) = frobComp k (lam ν k * c) := by
  ext x
  simp only [singAct_apply, conjAction_apply, frobComp_apply, lam]
  rw [mul_pow, Units.val_inv_eq_inv_val, inv_pow]
  ring

lemma singAct_mem_Mk (ν : (GaloisField 2 n)ˣ) {k : ℕ} {f : EndF n} (hf : f ∈ Mk k) :
    singAct ν f ∈ Mk k := by
  obtain ⟨c, rfl⟩ := mem_Mk.mp hf
  exact mem_Mk.mpr ⟨lam ν k * c, (singAct_frobComp ν k c).symm⟩

/-! ## The `pol` calculus -/

lemma pol_zero (k : ℕ) : pol (0 : EndF n) k = 0 := by
  rw [pol]
  rw [show (⇑(0 : EndF n) : GaloisField 2 n → GaloisField 2 n)
      = (0 : GaloisField 2 n → GaloisField 2 n) from rfl]
  rw [polyRep_zero, Polynomial.coeff_zero]

lemma pol_add (f g : EndF n) (k : ℕ) : pol (⇑(f + g)) k = pol f k + pol g k := by
  have h : (⇑(f + g) : GaloisField 2 n → GaloisField 2 n) = fun x => f x + g x := rfl
  simp only [pol, h, polyRep_add, Polynomial.coeff_add]

lemma pol_smul (a : ZMod 2) (f : EndF n) (k : ℕ) : pol (⇑(a • f)) k = a • pol f k := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · rw [zero_smul, zero_smul]
    exact pol_zero k
  · rw [one_smul, one_smul]

lemma pol_singAct_pow (ν : (GaloisField 2 n)ˣ) (k : ℕ) (hk : k < n) (i : ℕ) :
    ∀ f : EndF n, pol (((singAct ν) ^ i) f) k = (lam ν k) ^ i * pol f k := by
  induction i with
  | zero => intro f; simp
  | succ i ih =>
    intro f
    have h1 : ((singAct ν) ^ (i + 1)) f = ((singAct ν) ^ i) (singAct ν f) := by
      rw [pow_succ]; rfl
    rw [h1, ih (singAct ν f), singAct_apply, pol_conjAction (by omega : n ≠ 0) ν f hk,
      pow_succ, lam]
    ring

lemma pol_aeval_singAct (ν : (GaloisField 2 n)ˣ) (k : ℕ) (hk : k < n) (p : Polynomial (ZMod 2)) :
    ∀ f : EndF n, pol (Polynomial.aeval (singAct ν) p f) k
      = (Polynomial.aeval (lam ν k) p) * pol f k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro f
    have h1 : (Polynomial.aeval (singAct ν)) (p + q) f
        = (Polynomial.aeval (singAct ν)) p f + (Polynomial.aeval (singAct ν)) q f := by
      rw [Polynomial.aeval_add, LinearMap.add_apply]
    rw [h1, pol_add, hp f, hq f, Polynomial.aeval_add, add_mul]
  | monomial m a =>
    intro f
    have h1 : (Polynomial.aeval (singAct ν)) ((Polynomial.monomial m) a) f
        = a • (((singAct ν) ^ m) f) := by
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply,
        LinearMap.smul_apply, Module.End.one_apply]
    rw [h1, pol_smul, pol_singAct_pow ν k hk m f, Polynomial.aeval_monomial, Algebra.smul_def]
    ring

/-! ## The Frobenius decomposition -/

lemma frob_decomp (hn : n ≠ 0) (f : EndF n) :
    f = ∑ k ∈ Finset.range n, frobComp k (pol f k) := by
  ext x
  rw [LinearMap.sum_apply]
  simp only [frobComp_apply]
  exact frob_expansion hn (⇑f) f.map_add x

lemma eq_frobComp_of_supp_subset (hn : n ≠ 0) {f : EndF n} {k : ℕ} (hk : k < n)
    (h : ∀ j < n, j ≠ k → pol f j = 0) : f = frobComp k (pol f k) := by
  conv_lhs => rw [frob_decomp hn f]
  rw [Finset.sum_eq_single k]
  · intro j hj hjk
    rw [Finset.mem_range] at hj
    rw [h j hj hjk, frobComp_zero]
  · intro hknotin
    exact absurd (Finset.mem_range.mpr hk) hknotin

noncomputable def supp (f : EndF n) : Finset ℕ := (Finset.range n).filter (fun k => pol f k ≠ 0)

lemma mem_supp {f : EndF n} {k : ℕ} : k ∈ supp f ↔ k < n ∧ pol f k ≠ 0 := by
  simp [supp, Finset.mem_filter]

lemma eq_zero_of_forall_pol_eq_zero (hn : n ≠ 0) {f : EndF n} (h : ∀ k < n, pol f k = 0) :
    f = 0 := by
  rw [frob_decomp hn f]
  refine Finset.sum_eq_zero (fun k hk => ?_)
  rw [h k (Finset.mem_range.mp hk), frobComp_zero]

lemma ne_zero_iff_supp_nonempty (hn : n ≠ 0) {f : EndF n} : f ≠ 0 ↔ (supp f).Nonempty := by
  constructor
  · intro hf
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    refine hf (eq_zero_of_forall_pol_eq_zero hn (fun k hk => ?_))
    by_contra hne
    have hmem : k ∈ supp f := mem_supp.mpr ⟨hk, hne⟩
    rw [hc] at hmem
    simp at hmem
  · rintro ⟨k, hk⟩ hf
    obtain ⟨-, hk2⟩ := mem_supp.mp hk
    rw [hf] at hk2
    exact hk2 (pol_zero k)

/-! ## The eigenvalue/conjugacy input -/

lemma lam_minpoly_aeval (hn : 2 ≤ n) (ν : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1)
    {k k₂ : ℕ} (hk : k < n) (hk₂ : k₂ < n) :
    (Polynomial.aeval (lam ν k)) (minpoly (ZMod 2) (lam ν k₂)) = 0 ↔ k = k₂ := by
  constructor
  · intro h
    have hconj : IsConjRoot (ZMod 2) (lam ν k₂) (lam ν k) :=
      isConjRoot_of_aeval_eq_zero (Algebra.IsIntegral.isIntegral _) h
    obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
    obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (k := ZMod 2) (p := 2)
      (GaloisField 2 n) σ
    have h3 : σ (lam ν k) = (lam ν k) ^ (2 ^ i) := by simpa using hi (lam ν k)
    have h2 : lam ν k₂ = (lam ν k) ^ (2 ^ i) := by rw [← hσ, h3]
    exact (lam_frob_inj hn ν hν hk₂ hk h2).symm
  · intro h
    subst h
    exact minpoly.aeval (ZMod 2) (lam ν k)

/-! ## Reduction of the support -/

lemma supp_aeval_minpoly (hn : 2 ≤ n) (ν : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1)
    {k₀ : ℕ} (hk₀ : k₀ < n) (f : EndF n) :
    supp (Polynomial.aeval (singAct ν) (minpoly (ZMod 2) (lam ν k₀)) f)
      = (supp f).erase k₀ := by
  ext j
  rw [mem_supp, Finset.mem_erase, mem_supp]
  constructor
  · rintro ⟨hjn, hne⟩
    have hcoef := pol_aeval_singAct ν j hjn (minpoly (ZMod 2) (lam ν k₀)) f
    have hμ : (Polynomial.aeval (lam ν j)) (minpoly (ZMod 2) (lam ν k₀)) ≠ 0 := by
      intro hz
      exact hne (by rw [hcoef, hz, zero_mul])
    have hjk : j ≠ k₀ := by
      rintro rfl
      exact hμ ((lam_minpoly_aeval hn ν hν hjn hk₀).mpr rfl)
    have hfj : pol f j ≠ 0 := by
      intro hz
      exact hne (by rw [hcoef, hz, mul_zero])
    exact ⟨hjk, hjn, hfj⟩
  · rintro ⟨hjk, hjn, hfj⟩
    refine ⟨hjn, ?_⟩
    have hcoef := pol_aeval_singAct ν j hjn (minpoly (ZMod 2) (lam ν k₀)) f
    have hμ : (Polynomial.aeval (lam ν j)) (minpoly (ZMod 2) (lam ν k₀)) ≠ 0 := by
      intro hz
      exact hjk ((lam_minpoly_aeval hn ν hν hjn hk₀).mp hz)
    rw [hcoef]
    exact mul_ne_zero hμ hfj

/-! ## Frobenius monomials with non-zero coefficient are bijections -/

lemma frobComp_bijective {k : ℕ} {c : GaloisField 2 n} (hc : c ≠ 0) :
    Function.Bijective (frobComp k c) := by
  have hpow_ne : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hinj : Function.Injective (frobComp k c) := by
    intro x y hxy
    simp only [frobComp_apply] at hxy
    have h1 : x ^ (2 ^ k) = y ^ (2 ^ k) := mul_left_cancel₀ hc hxy
    have h2 : (x + y) ^ (2 ^ k) = 0 := by
      rw [add_pow_char_pow, h1]
      exact add_self_eq_zero_zmod2' _
    have h3 : x + y = 0 := (pow_eq_zero_iff hpow_ne).mp h2
    calc x = -y := add_eq_zero_iff_eq_neg.mp h3
      _ = y := neg_eq_self_zmod2' y
  exact ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩

/-! ## The cyclic submodule generated by an element -/

lemma pow_singAct_mem {T : Submodule (ZMod 2) (EndF n)} {ν : (GaloisField 2 n)ˣ}
    (hTξ : ∀ f ∈ T, singAct ν f ∈ T) (i : ℕ) : ∀ g ∈ T, ((singAct ν) ^ i) g ∈ T := by
  induction i with
  | zero => intro g hg; simpa using hg
  | succ i ih =>
    intro g hg
    have h1 : ((singAct ν) ^ (i + 1)) g = ((singAct ν) ^ i) (singAct ν g) := by
      rw [pow_succ]; rfl
    rw [h1]
    exact ih _ (hTξ g hg)

lemma aeval_mem {T : Submodule (ZMod 2) (EndF n)} {ν : (GaloisField 2 n)ˣ}
    (hTξ : ∀ f ∈ T, singAct ν f ∈ T) {g : EndF n} (hg : g ∈ T) (p : Polynomial (ZMod 2)) :
    (Polynomial.aeval (singAct ν)) p g ∈ T := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.aeval_add, LinearMap.add_apply]; exact T.add_mem hp hq
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    exact T.smul_mem _ (pow_singAct_mem hTξ m g hg)

noncomputable def polEval (ν : (GaloisField 2 n)ˣ) (g : EndF n) :
    Polynomial (ZMod 2) →ₗ[ZMod 2] (EndF n) where
  toFun p := Polynomial.aeval (singAct ν) p g
  map_add' p q := by rw [Polynomial.aeval_add, LinearMap.add_apply]
  map_smul' a p := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] lemma polEval_apply (ν : (GaloisField 2 n)ˣ) (g : EndF n) (p : Polynomial (ZMod 2)) :
    polEval ν g p = Polynomial.aeval (singAct ν) p g := rfl

/-! ## The field-level Frobenius-component theorem -/

theorem frob_component_bijective_aux {n : ℕ} (hn : 2 ≤ n)
    (ν : (GaloisField 2 n)ˣ) (hν : orderOf ν = 2 ^ n - 1)
    (T : Submodule (ZMod 2) (EndF n))
    (hTξ : ∀ f ∈ T, singAct ν f ∈ T)
    (hirr : ∀ T' : Submodule (ZMod 2) (EndF n),
      (∀ f ∈ T', singAct ν f ∈ T') → T' ≤ T → T' = ⊥ ∨ T' = T) :
    ∀ f ∈ T, f ≠ 0 → Function.Bijective f := by
  intro f hfT hf
  have hn0 : n ≠ 0 := by omega
  have key : ∀ m : ℕ, ∀ f ∈ T, f ≠ 0 → (supp f).card ≤ m →
      ∃ g ∈ T, g ≠ 0 ∧ (supp g).card = 1 := by
    intro m
    induction m with
    | zero =>
      intro f hfT hf hle
      have hpos : 0 < (supp f).card := Finset.card_pos.mpr ((ne_zero_iff_supp_nonempty hn0).mp hf)
      omega
    | succ m ih =>
      intro f hfT hf hle
      rcases Nat.lt_or_ge (supp f).card 2 with hlt | hge
      · refine ⟨f, hfT, hf, ?_⟩
        have hpos : 0 < (supp f).card := Finset.card_pos.mpr ((ne_zero_iff_supp_nonempty hn0).mp hf)
        omega
      · obtain ⟨k₀, hk₀⟩ := Finset.card_pos.mp (by omega : 0 < (supp f).card)
        have hk₀n : k₀ < n := (mem_supp.mp hk₀).1
        have hgp : Polynomial.aeval (singAct ν) (minpoly (ZMod 2) (lam ν k₀)) f ∈ T :=
          aeval_mem hTξ hfT (minpoly (ZMod 2) (lam ν k₀))
        refine ih _ hgp ?_ ?_
        · rw [ne_zero_iff_supp_nonempty hn0, supp_aeval_minpoly hn ν hν hk₀n f]
          exact Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hk₀]; omega)
        · rw [supp_aeval_minpoly hn ν hν hk₀n f, Finset.card_erase_of_mem hk₀]
          omega
  obtain ⟨g, hgT, hg, hgcard⟩ := key (supp f).card f hfT hf le_rfl
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hgcard
  have hkmem : k ∈ supp g := by rw [hk]; exact Finset.mem_singleton_self k
  have hkn : k < n := (mem_supp.mp hkmem).1
  have hgMk : g ∈ Mk k := by
    refine mem_Mk.mpr ⟨pol g k, ?_⟩
    refine (eq_frobComp_of_supp_subset hn0 hkn ?_).symm
    intro j hj hjk
    by_contra hne
    have hjm : j ∈ supp g := mem_supp.mpr ⟨hj, hne⟩
    rw [hk, Finset.mem_singleton] at hjm
    exact hjk hjm
  let T' : Submodule (ZMod 2) (EndF n) := LinearMap.range (polEval ν g)
  have hT'le : T' ≤ T := by
    rintro h ⟨p, rfl⟩
    exact aeval_mem hTξ hgT p
  have hT'stab : ∀ h ∈ T', singAct ν h ∈ T' := by
    rintro h ⟨p, rfl⟩
    refine ⟨Polynomial.X * p, ?_⟩
    rw [polEval_apply, polEval_apply, Polynomial.aeval_mul, Polynomial.aeval_X,
      Module.End.mul_apply]
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    have hmem : g ∈ T' := ⟨1, by rw [polEval_apply, map_one, Module.End.one_apply]⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hg hmem
  have hT'T : T' = T := by
    rcases hirr T' hT'stab hT'le with h | h
    · exact absurd h hT'ne
    · exact h
  have hT'Mk : T' ≤ Mk k := by
    rintro h ⟨p, rfl⟩
    exact aeval_mem (T := Mk k) (fun f hf => singAct_mem_Mk ν hf) hgMk p
  have hfMk : f ∈ Mk k := hT'Mk (hT'T.symm ▸ hfT)
  obtain ⟨c, hc⟩ := mem_Mk.mp hfMk
  have hcne : c ≠ 0 := by
    intro hc0
    exact hf (by rw [← hc, hc0, frobComp_zero])
  rw [← hc]
  exact frobComp_bijective hcne


end FSB

open FSB

/-- **A nonzero irreducible `𝔽₂⟨ξ⟩`-submodule of `Hom(S,W)`, for cyclic `𝔽₂⟨ξ⟩`-modules `S`, `W`
of the same order `2^n` (`n ≥ 2`), consists of zero or bijections.** -/
theorem frob_submodule_bijective
    {S W : Type} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {n : ℕ} (hn : 2 ≤ n) (hS : Nat.card S = 2 ^ n) (hW : Nat.card W = 2 ^ n)
    (ξS : S ≃ₗ[ZMod 2] S) (ξW : W ≃ₗ[ZMod 2] W)
    (hSt : ∀ a b : S, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξS ^ k) a = b)
    (hWt : ∀ a b : W, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξW ^ k) a = b)
    (ψ : S ≃ₗ[ZMod 2] W) (hψ : ∀ s : S, ψ (ξS s) = ξW (ψ s))
    (T : Submodule (ZMod 2) (S →ₗ[ZMod 2] W))
    (hTξ : ∀ f ∈ T, ξW.toLinearMap.comp (f.comp ξS.symm.toLinearMap) ∈ T)
    (hirr : ∀ T' : Submodule (ZMod 2) (S →ₗ[ZMod 2] W),
      (∀ f ∈ T', ξW.toLinearMap.comp (f.comp ξS.symm.toLinearMap) ∈ T') →
      T' ≤ T → T' = ⊥ ∨ T' = T) :
    ∀ f ∈ T, f ≠ 0 → Function.Bijective f := by
  classical
  -- ## Singer coordinates on `S`
  obtain ⟨hSord, hSfree⟩ := Work.Higman.singer_data_of_transitive hn hS ξS hSt
  obtain ⟨φS, lamS, hlamSord, hφSp⟩ :=
    Work.Higman.exists_singer_iso (n := n) (V := S) (by omega : 0 < n) hS ξS hSord hSfree
  -- ## The alignment identities
  have hψsym : ∀ w : W, ψ.symm (ξW w) = ξS (ψ.symm w) := by
    intro w
    obtain ⟨s, rfl⟩ := ψ.surjective w
    rw [← hψ s, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hφSinv : ∀ v : GaloisField 2 n,
      φS (ξS.symm (φS.symm v)) = ((lamS⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * v := by
    intro v
    have h1 := hφSp (ξS.symm (φS.symm v))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    have hw : (↑lamS : GaloisField 2 n) * φS (ξS.symm (φS.symm v)) = v := h1.symm
    have hlamne : (↑lamS : GaloisField 2 n) ≠ 0 := Units.ne_zero lamS
    calc φS (ξS.symm (φS.symm v))
        = (↑lamS : GaloisField 2 n)⁻¹
            * ((↑lamS : GaloisField 2 n) * φS (ξS.symm (φS.symm v))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hlamne, one_mul]
      _ = (↑lamS : GaloisField 2 n)⁻¹ * v := by rw [hw]
      _ = ((lamS⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * v := by
          rw [Units.val_inv_eq_inv_val]
  have hξφ : ∀ y : GaloisField 2 n,
      ξS.symm (φS.symm y)
        = φS.symm (((lamS⁻¹ : (GaloisField 2 n)ˣ) : GaloisField 2 n) * y) := by
    intro y
    apply φS.injective
    rw [hφSinv y, LinearEquiv.apply_symm_apply]
  -- ## The transport `Φ`
  let Φ : (S →ₗ[ZMod 2] W) →ₗ[ZMod 2] (GaloisField 2 n →ₗ[ZMod 2] GaloisField 2 n) :=
    { toFun := fun f => φS.toLinearMap.comp (ψ.symm.toLinearMap.comp (f.comp φS.symm.toLinearMap))
      map_add' := by
        intro f g
        ext x
        simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
      map_smul' := by
        intro a f
        ext x
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply] }
  have hΦapply : ∀ (f : S →ₗ[ZMod 2] W) (x : GaloisField 2 n),
      Φ f x = φS (ψ.symm (f (φS.symm x))) := by
    intro f x
    rw [show Φ f x
        = (φS.toLinearMap.comp (ψ.symm.toLinearMap.comp (f.comp φS.symm.toLinearMap))) x from rfl,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap]
  have hΦact : ∀ f : S →ₗ[ZMod 2] W,
      Φ (ξW.toLinearMap.comp (f.comp ξS.symm.toLinearMap)) = conjAction lamS (Φ f) := by
    intro f
    ext y
    rw [hΦapply, conjAction_apply, hΦapply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [hψsym, hξφ y, hφSp, Units.val_inv_eq_inv_val]
  -- ## Injectivity of `Φ`
  have hΦker : ∀ f : S →ₗ[ZMod 2] W, Φ f = 0 → f = 0 := by
    intro f hf
    ext x
    obtain ⟨y, rfl⟩ := φS.symm.surjective x
    have h1 : Φ f y = 0 := by rw [hf]; rfl
    rw [hΦapply] at h1
    have h2 : ψ.symm (f (φS.symm y)) = 0 := φS.injective (by rw [h1, map_zero])
    exact ψ.symm.injective (by rw [h2, LinearMap.zero_apply, map_zero])
  have hΦinj : Function.Injective Φ := by
    intro f g hfg
    have h0 : Φ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
    exact sub_eq_zero.mp (hΦker (f - g) h0)
  -- ## The field-level theorem applies to `T.map Φ`
  have hbijf : ∀ f ∈ T.map Φ, f ≠ 0 → Function.Bijective f := by
    refine FSB.frob_component_bijective_aux hn lamS hlamSord (T.map Φ) ?_ ?_
    · rintro h ⟨g, hgT, rfl⟩
      rw [FSB.singAct_apply, ← hΦact g]
      exact Submodule.mem_map.mpr ⟨ξW.toLinearMap.comp (g.comp ξS.symm.toLinearMap), hTξ g hgT,
        rfl⟩
    · intro T'' hT''ξ hT''le
      set T₀ : Submodule (ZMod 2) (S →ₗ[ZMod 2] W) := Submodule.comap Φ T'' with hT₀
      have hT₀stab : ∀ f ∈ T₀, ξW.toLinearMap.comp (f.comp ξS.symm.toLinearMap) ∈ T₀ := by
        intro f hf
        rw [hT₀, Submodule.mem_comap] at hf ⊢
        rw [hΦact f]
        simpa only [FSB.singAct_apply] using hT''ξ (Φ f) hf
      have hT₀le : T₀ ≤ T := by
        intro f hf
        rw [hT₀, Submodule.mem_comap] at hf
        obtain ⟨t, htT, htx⟩ := Submodule.mem_map.mp (hT''le hf)
        rw [← hΦinj htx]
        exact htT
      have hmap : T₀.map Φ = T'' := by
        refine le_antisymm (Submodule.map_comap_le Φ T'') ?_
        intro x hx
        obtain ⟨t, htT, htx⟩ := Submodule.mem_map.mp (hT''le hx)
        refine Submodule.mem_map.mpr ⟨t, ?_, htx⟩
        rw [hT₀, Submodule.mem_comap, htx]
        exact hx
      rcases hirr T₀ hT₀stab hT₀le with h | h
      · left
        rw [← hmap, h, Submodule.map_bot]
      · right
        rw [← hmap, h]
  -- ## Conclude
  intro f hfT hf
  have hmem : Φ f ∈ T.map Φ := Submodule.mem_map.mpr ⟨f, hfT, rfl⟩
  have hne : Φ f ≠ 0 := fun h0 => hf (hΦker f h0)
  have hbij : Function.Bijective (Φ f) := hbijf (Φ f) hmem hne
  have hfeq : ∀ x : S, f x = ψ (φS.symm ((Φ f) (φS x))) := by
    intro x
    have h1 : (Φ f) (φS x) = φS (ψ.symm (f x)) := by
      rw [hΦapply, LinearEquiv.symm_apply_apply]
    rw [h1, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  have hinj : Function.Injective (fun x : S => ψ (φS.symm ((Φ f) (φS x)))) := by
    intro x y hxy
    have h1 : φS.symm ((Φ f) (φS x)) = φS.symm ((Φ f) (φS y)) := ψ.injective hxy
    have h2 : (Φ f) (φS x) = (Φ f) (φS y) := φS.symm.injective h1
    exact φS.injective (hbij.1 h2)
  have hsurj : Function.Surjective (fun x : S => ψ (φS.symm ((Φ f) (φS x)))) := by
    intro y
    obtain ⟨z, hz⟩ := hbij.2 (φS (ψ.symm y))
    refine ⟨φS.symm z, ?_⟩
    show ψ (φS.symm ((Φ f) (φS (φS.symm z)))) = y
    rw [LinearEquiv.apply_symm_apply, hz, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  have hbij' : Function.Bijective (fun x : S => ψ (φS.symm ((Φ f) (φS x)))) := ⟨hinj, hsurj⟩
  rw [funext hfeq]
  exact hbij'

end Work.Higman.H8
