import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

theorem comap_eq_self_iff_val_eq_of_isAlgebraic {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : Algebra.IsAlgebraic K L) (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    A.comap (σ : L →+* L) = A ↔ ∀ x : L, A.valuation (σ x) = A.valuation x := by
  classical
  constructor
  · intro h x
    -- `h` says `σ` preserves `A`
    have hA : ∀ z : L, z ∈ A ↔ σ z ∈ A := by
      intro z
      have hz := SetLike.ext_iff.mp h z
      rw [ValuationSubring.mem_comap] at hz
      exact hz.symm
    -- shifting by `σ` preserves the order on the value group
    have key : ∀ y z : L, A.valuation y ≤ A.valuation z ↔
        A.valuation (σ y) ≤ A.valuation (σ z) := by
      intro y z
      constructor
      · intro hle
        rw [ValuationSubring.valuation_le_iff] at hle ⊢
        obtain ⟨a, haeq⟩ := hle
        exact ⟨⟨σ a, (hA a).mp a.2⟩, by rw [← map_mul, haeq]⟩
      · intro hle
        rw [ValuationSubring.valuation_le_iff] at hle ⊢
        obtain ⟨a, haeq⟩ := hle
        refine ⟨⟨σ.symm a, (hA _).mpr (by simpa only [AlgEquiv.apply_symm_apply] using a.2)⟩, ?_⟩
        have h2 : σ.symm ((a : L) * σ z) = σ.symm (σ y) := by rw [haeq]
        rw [map_mul] at h2
        simpa only [AlgEquiv.symm_apply_apply, map_mul] using h2
    -- the orbit of `x` under `σ` is finite: all its elements are roots of a polynomial
    obtain ⟨p, hp_ne, hp_root⟩ := halg.isAlgebraic x
    let q : Polynomial L := p.map (algebraMap K L)
    have hq_ne : q ≠ 0 := by
      intro hq
      refine hp_ne (Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective ?_)
      rw [Polynomial.map_zero]
      simpa [q] using hq
    have hroot : ∀ n : ℕ, (σ ^ n) x ∈ q.roots := by
      intro n
      rw [Polynomial.mem_roots hq_ne, Polynomial.IsRoot.def]
      have haeval : Polynomial.aeval ((σ ^ n) x) p = 0 := by
        induction n with
        | zero => simpa using hp_root
        | succ n ih =>
          rw [pow_succ', AlgEquiv.mul_apply, Polynomial.aeval_algHom_apply, ih, map_zero]
      have : Polynomial.eval ((σ ^ n) x) q = Polynomial.aeval ((σ ^ n) x) p := by
        rw [Polynomial.eval_map, Polynomial.aeval_def]
      rw [this, haeval]
    have hcard_le : q.roots.toFinset.card ≤ p.natDegree := by
      refine (Multiset.toFinset_card_le q.roots).trans ?_
      have h1 : (q.roots.card : WithBot ℕ) ≤ (p.natDegree : WithBot ℕ) := by
        calc (q.roots.card : WithBot ℕ) ≤ q.degree := Polynomial.card_roots hq_ne
          _ = (p.natDegree : WithBot ℕ) := by
                rw [Polynomial.degree_eq_natDegree hq_ne,
                  Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective p]
      exact WithBot.coe_le_coe.mp h1
    have hsub : (Finset.range (p.natDegree + 1)).image (fun n => (σ ^ n) x) ⊆ q.roots.toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨n, -, rfl⟩ := hy
      rw [Multiset.mem_toFinset]
      exact hroot n
    have hex : ∃ i j : ℕ, i < j ∧ (σ ^ i) x = (σ ^ j) x := by
      by_contra hc
      push Not at hc
      have hinj : Function.Injective (fun n : ℕ => (σ ^ n) x) := by
        intro a b hab
        rcases lt_trichotomy a b with hlt | heq | hgt
        · exact absurd hab (hc a b hlt)
        · exact heq
        · exact absurd hab.symm (hc b a hgt)
      have hcard_eq : (Finset.image (fun n => (σ ^ n) x) (Finset.range (p.natDegree + 1))).card
          = p.natDegree + 1 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      have hle := (Finset.card_le_card hsub).trans hcard_le
      omega
    obtain ⟨i, j, hij, heq⟩ := hex
    have hpow : (σ ^ (j - i)) x = x := by
      have h1 : (σ ^ j) x = (σ ^ i) ((σ ^ (j - i)) x) := by
        conv_lhs => rw [show j = i + (j - i) from by omega]
        rw [pow_add, AlgEquiv.mul_apply]
      rw [h1] at heq
      exact ((σ ^ i).injective heq).symm
    set k : ℕ := j - i with hkdef
    have hk_pos : 0 < k := by omega
    have hk : (σ ^ k) x = x := by rw [hkdef]; exact hpow
    let g : ℕ → A.ValueGroup := fun n => A.valuation ((σ ^ n) x)
    have hg_period : ∀ n : ℕ, g (n + k) = g n := by
      intro n
      change A.valuation ((σ ^ (n + k)) x) = A.valuation ((σ ^ n) x)
      rw [pow_add, AlgEquiv.mul_apply, hk]
    have hg_shift : ∀ a b : ℕ, g a ≤ g b ↔ g (a + 1) ≤ g (b + 1) := by
      intro a b
      change A.valuation ((σ ^ a) x) ≤ A.valuation ((σ ^ b) x) ↔
        A.valuation ((σ ^ (a + 1)) x) ≤ A.valuation ((σ ^ (b + 1)) x)
      rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      exact key ((σ ^ a) x) ((σ ^ b) x)
    have hwdef : ∀ a b : ℕ, g a = g b → g (a + 1) = g (b + 1) := by
      intro a b hab
      exact le_antisymm ((hg_shift a b).mp (le_of_eq hab))
        ((hg_shift b a).mp (le_of_eq hab.symm))
    let S : Finset A.ValueGroup := (Finset.range k).image g
    have hg0S : g 0 ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk_pos, rfl⟩
    have hmem_shift : ∀ m : ℕ, m < k → g (m + 1) ∈ S := by
      intro m hm
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hm) with h | h
      · exact Finset.mem_image.mpr ⟨m + 1, Finset.mem_range.mpr h, rfl⟩
      · refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk_pos, ?_⟩
        rw [show m + 1 = k from by omega]
        simpa using (hg_period 0).symm
    let nOf : ↥(↑S : Set A.ValueGroup) → ℕ := fun s =>
      Classical.choose (Finset.mem_image.mp (Finset.mem_coe.mp s.2))
    have nOf_spec : ∀ s : ↥(↑S : Set A.ValueGroup), g (nOf s) = s.1 ∧ nOf s < k := by
      intro s
      have hc := Classical.choose_spec (Finset.mem_image.mp (Finset.mem_coe.mp s.2))
      rw [Finset.mem_range] at hc
      exact ⟨hc.2, hc.1⟩
    let τ : ↥(↑S : Set A.ValueGroup) →o ↥(↑S : Set A.ValueGroup) :=
      { toFun := fun s => ⟨g (nOf s + 1), by
          rw [Finset.mem_coe]
          exact hmem_shift (nOf s) (nOf_spec s).2⟩
        monotone' := by
          intro s t hst
          show g (nOf s + 1) ≤ g (nOf t + 1)
          exact (hg_shift (nOf s) (nOf t)).mp
            (by rw [(nOf_spec s).1, (nOf_spec t).1]; exact hst) }
    have hτinj : Function.Injective τ := by
      intro s t hst
      apply Subtype.ext
      have h1 : g (nOf s + 1) = g (nOf t + 1) := by
        show (τ s).1 = (τ t).1
        exact congrArg Subtype.val hst
      have h2 : g (nOf s) = g (nOf t) :=
        le_antisymm ((hg_shift (nOf s) (nOf t)).mpr (le_of_eq h1))
          ((hg_shift (nOf t) (nOf s)).mpr (le_of_eq h1.symm))
      rw [← (nOf_spec s).1, ← (nOf_spec t).1]
      exact h2
    have hid := OrderHom.eq_id_of_injective τ hτinj
    have hmem0 : g 0 ∈ (↑S : Set A.ValueGroup) := Finset.mem_coe.mpr hg0S
    let s0 : ↥(↑S : Set A.ValueGroup) := ⟨g 0, hmem0⟩
    have hval : (τ s0).1 = g 0 := by
      have h : τ s0 = s0 := congrArg (fun f => f s0) hid
      exact congrArg Subtype.val h
    have hchoose : g (nOf s0 + 1) = g 1 := by
      have h0 : g (nOf s0) = g 0 := (nOf_spec s0).1
      have hstep := hwdef (nOf s0) 0 h0
      simpa using hstep
    have hg10 : g 1 = g 0 := by
      rw [← hchoose, ← hval]
      rfl
    have hlhs : g 1 = A.valuation (σ x) := by
      change A.valuation ((σ ^ 1) x) = A.valuation (σ x)
      rw [pow_one]
    have hrhs : g 0 = A.valuation x := by
      change A.valuation ((σ ^ 0) x) = A.valuation x
      rw [pow_zero, AlgEquiv.one_apply]
    rw [← hlhs, ← hrhs]
    exact hg10
  · intro h
    ext z
    rw [ValuationSubring.mem_comap]
    have hz : A.valuation ((σ : L →+* L) z) = A.valuation z := h z
    rw [← ValuationSubring.valuation_le_one_iff, hz, ValuationSubring.valuation_le_one_iff]

end Commons.RingTheory.Valuation