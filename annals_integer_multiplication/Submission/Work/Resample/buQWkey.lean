import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.egSigTKey

/-!
# `Work.Resample.buQWkey`

The index arithmetic behind the selection stage `buSelL` of the one-dimensional `B̃` word
(paper Prop. 4.7(ii)): the fused map `ν = C̃ ∘ P̃_t`, `ν ℓ = σ_t [tℓ/s] = egNu s t ℓ`, is an
injective map from `Fin s` into `{0,…,t-1}`, and the "key" map `egLam s t` used by the
`Label and sort` implementation of the selection is its inverse on the image and `s+i` off it.
-/

set_option autoImplicit false

namespace Work.Resample

/-! ## The rounding index `egRho` -/

/-- `⌊x/c⌋ + ⌊y/c⌋ ≤ ⌊(x+y)/c⌋` (the floor of a sum dominates the sum of the floors). -/
lemma div_add_div_le (A B c : ℕ) (hc : 0 < c) : A / c + B / c ≤ (A + B) / c := by
  rw [Nat.le_div_iff_mul_le hc, Nat.add_mul]
  exact Nat.add_le_add (Nat.div_mul_le_self A c) (Nat.div_mul_le_self B c)

/-- `egRho s t` is strictly increasing as soon as `s < t`: the numerator grows by `2t ≥ 2s+2`
per unit step of the argument, so the rounded quotient grows by at least one. -/
lemma egRho_lt_add (s t a c : ℕ) (hs : 0 < s) (hst : s < t) (hc : 0 < c) :
    egRho s t a < egRho s t (a + c) := by
  have h2s : 0 < 2 * s := by omega
  have hP : 2 * t * (a + c) + s = (2 * t * a + s) + 2 * t * c := by ring
  have hQ : 1 ≤ (2 * t * c) / (2 * s) := by
    rw [Nat.le_div_iff_mul_le h2s]
    have h2 : 2 * t ≤ 2 * t * c := by
      calc 2 * t = 2 * t * 1 := by ring
        _ ≤ 2 * t * c := Nat.mul_le_mul_left (2 * t) hc
    have h3 : 2 * s ≤ 2 * t := by omega
    simpa using le_trans h3 h2
  have hmain := div_add_div_le (2 * t * a + s) (2 * t * c) (2 * s) h2s
  rw [egRho, egRho, hP]
  omega

lemma egRho_strictMono (s t : ℕ) (hs : 0 < s) (hst : s < t) : StrictMono (egRho s t) := by
  intro a b hab
  obtain ⟨c, hc⟩ : ∃ c, b = a + c := ⟨b - a, (Nat.add_sub_of_le (le_of_lt hab)).symm⟩
  have hc0 : 0 < c := by omega
  subst hc
  exact egRho_lt_add s t a c hs hst hc0

/-- `egRho s t s = t`: the rounding map sends the endpoint `s` exactly to `t`. -/
lemma egRho_self (s t : ℕ) (hs : 0 < s) : egRho s t s = t := by
  have h2s : 0 < 2 * s := by omega
  rw [egRho]
  refine le_antisymm ?_ ?_
  · have h : (2 * t * s + s) / (2 * s) < t + 1 := by
      rw [Nat.div_lt_iff_lt_mul h2s]
      have hcast : (t + 1) * (2 * s) = 2 * t * s + 2 * s := by ring
      rw [hcast]
      omega
    omega
  · rw [Nat.le_div_iff_mul_le h2s]
    have hcast : t * (2 * s) = 2 * t * s := by ring
    rw [hcast]
    omega

/-- The row index `[tℓ/s] = egRho s t ℓ` of `C̃` lies below `t` for `ℓ < s`. -/
private lemma egRho_lt (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ : ℕ) (hℓ : ℓ < s) :
    egRho s t ℓ < t := by
  have h := egRho_strictMono s t hs hst hℓ
  rwa [egRho_self s t hs] at h

/-! ## The fused index map `egNu` -/

/-- The fused index `ν ℓ = σ_t [tℓ/s]` lands in `{0,…,t-1}`. -/
lemma egNu_lt (s t : ℕ) (ht : 0 < t) (ℓ : Fin s) : egNu s t (ℓ : ℕ) < t := by
  simp only [egNu, egSigT]
  exact Nat.mod_lt _ ht

/-- The fused index map `ν = σ_t ∘ egRho` is injective on `Fin s`: `egRho` is strictly increasing
and `σ_t k = (-s k) mod t` is injective on `{0,…,t-1}` since `gcd s t = 1`. -/
private lemma egNu_inj (s t : ℕ) (hs : 0 < s) (hst : s < t) (hcop : Nat.Coprime s t) :
    Function.Injective (fun ℓ : Fin s => egNu s t (ℓ : ℕ)) := by
  have ht : 0 < t := lt_of_lt_of_le hs (le_of_lt hst)
  intro ℓ ℓ' h
  have h1 : egRho s t (ℓ : ℕ) = egRho s t (ℓ' : ℕ) :=
    (egSigTKey s t hcop ht).2 _ _
      (egRho_lt s t hs hst _ ℓ.isLt) (egRho_lt s t hs hst _ ℓ'.isLt) h
  exact Fin.ext ((egRho_strictMono s t hs hst).injective h1)

/-! ## The key map `egLam` -/

/-- On the image of `ν`, the key of `i` is the index of the unique `ℓ` with `ν ℓ = i`. -/
private lemma egLam_of_mem (s t i : ℕ) (h : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i) :
    egLam s t i = ((Classical.choose h : Fin s) : ℕ) :=
  dite_eq_left h

/-- Off the image of `ν`, the key of `i` is `s + i` (so that it sorts after all the selected
indices). -/
private lemma egLam_of_not (s t i : ℕ) (h : ¬ ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i) :
    egLam s t i = s + i :=
  dite_eq_right h

/-- On the image of `ν`, the key is `< s`. -/
lemma egLam_lt_of_mem (s t i : ℕ) (h : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i) :
    egLam s t i < s := by
  rw [egLam_of_mem s t i h]
  exact (Classical.choose h).isLt

/-- `egLam` is a left inverse of `ν` (as an index map): on the image of `ν`, `ν (egLam i) = i`. -/
lemma egNu_egLam (s t i : ℕ) (h : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i) :
    egNu s t (egLam s t i) = i := by
  rw [egLam_of_mem s t i h]
  exact Classical.choose_spec h

/-- `egLam s t` is injective on `{0,…,t-1}`: two selected indices have distinct keys `< s`, two
unselected ones have distinct keys `s+i`, and a selected key is `< s` while an unselected one is
`≥ s`. -/
lemma egLam_inj (s t : ℕ) (hs : 0 < s) (hst : s < t) (hcop : Nat.Coprime s t) :
    ∀ i j : ℕ, i < t → j < t → egLam s t i = egLam s t j → i = j := by
  intro i j _ _ hij
  by_cases hPi : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i
  · by_cases hPj : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = j
    · rw [egLam_of_mem s t i hPi, egLam_of_mem s t j hPj] at hij
      exact (Classical.choose_spec hPi).symm.trans
        ((congrArg (egNu s t) hij).trans (Classical.choose_spec hPj))
    · rw [egLam_of_mem s t i hPi, egLam_of_not s t j hPj] at hij
      have := (Classical.choose hPi).isLt
      omega
  · by_cases hPj : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = j
    · rw [egLam_of_not s t i hPi, egLam_of_mem s t j hPj] at hij
      have := (Classical.choose hPj).isLt
      omega
    · rw [egLam_of_not s t i hPi, egLam_of_not s t j hPj] at hij
      omega

/-! ## The target -/

theorem buQWkey (s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t) :
    (∀ ℓ : Fin s, Work.Resample.egNu s t (ℓ : ℕ) < t) ∧
    (Function.Injective fun ℓ : Fin s => Work.Resample.egNu s t (ℓ : ℕ)) ∧
    (∀ (i : ℕ) (ℓ : Fin s), Work.Resample.egNu s t (ℓ : ℕ) = i → Work.Resample.egLam s t i = (ℓ : ℕ)) ∧
    (∀ i < t, (Work.Resample.egLam s t i < s) ↔ ∃ ℓ : Fin s, Work.Resample.egNu s t (ℓ : ℕ) = i) ∧
    (∀ i < t, (Work.Resample.egLam s t i = s + i) ↔ ¬∃ ℓ : Fin s, Work.Resample.egNu s t (ℓ : ℕ) = i) ∧
    ((List.ofFn fun i : Fin t => (Work.Resample.egLam s t i : ℤ))).Nodup ∧
    (∀ i < t, 0 ≤ (Work.Resample.egLam s t i : ℤ)) ∧
    (∀ i < t, Work.Resample.egLam s t i ≤ s + i) ∧
    (∀ ℓ < s, ∃ i < t, Work.Resample.egLam s t i = ℓ) := by
  have hs0 : 0 < s := by omega
  have ht : 0 < t := by omega
  have hnu_inj : Function.Injective (fun ℓ : Fin s => egNu s t (ℓ : ℕ)) :=
    egNu_inj s t hs0 hst hcop
  have hlam_inj := egLam_inj s t hs0 hst hcop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ
    exact egNu_lt s t ht ℓ
  · exact hnu_inj
  · intro i ℓ hν
    have h : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i := ⟨ℓ, hν⟩
    rw [egLam_of_mem s t i h]
    exact congrArg Fin.val (hnu_inj ((Classical.choose_spec h).trans hν.symm))
  · intro i _
    constructor
    · intro hlt
      by_contra hcon
      rw [egLam_of_not s t i hcon] at hlt
      omega
    · rintro ⟨ℓ, hν⟩
      exact egLam_lt_of_mem s t i ⟨ℓ, hν⟩
  · intro i _
    constructor
    · intro heq hcon
      rw [egLam_of_mem s t i hcon] at heq
      have := (Classical.choose hcon).isLt
      omega
    · intro hcon
      exact egLam_of_not s t i hcon
  · rw [List.nodup_ofFn]
    intro i j hij
    refine Fin.ext (hlam_inj (i : ℕ) (j : ℕ) i.isLt j.isLt ?_)
    exact Int.ofNat.inj hij
  · intro i _
    exact Int.natCast_nonneg _
  · intro i _
    by_cases h : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i
    · rw [egLam_of_mem s t i h]
      exact le_trans (Nat.le_of_lt (Classical.choose h).isLt) (Nat.le_add_right s i)
    · rw [egLam_of_not s t i h]
  · intro ℓ hℓ
    refine ⟨egNu s t ℓ, egNu_lt s t ht ⟨ℓ, hℓ⟩, ?_⟩
    have h : ∃ ℓ' : Fin s, egNu s t (ℓ' : ℕ) = egNu s t ℓ := ⟨⟨ℓ, hℓ⟩, rfl⟩
    rw [egLam_of_mem s t (egNu s t ℓ) h]
    have hchoose : (Classical.choose h : Fin s) = ⟨ℓ, hℓ⟩ := by
      apply hnu_inj
      change egNu s t ((Classical.choose h : Fin s) : ℕ) = egNu s t ((⟨ℓ, hℓ⟩ : Fin s) : ℕ)
      exact Classical.choose_spec h
    exact congrArg Fin.val hchoose

end Work.Resample
