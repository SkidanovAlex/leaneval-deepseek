import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.Combinatorics.MvPolynomial.grid_eval_ne_zero
import Submission.Commons.Algebra.MvPolynomial.exists_eval_ne_zero_of_totalDegree_le
import Submission.Commons.Algebra.MvPolynomial.finrank_restrictTotalDegree

namespace Commons.Algebra.MvPolynomial

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-! ### Basic setup -/

noncomputable def jetLinearMap (r : ℕ) (P : Fin r → 𝕜) :
    MvPolynomial (Fin r) 𝕜 →ₗ[𝕜] (Option (Fin r) → 𝕜) :=
  LinearMap.pi (fun k => match k with
    | none => (MvPolynomial.aeval (R := 𝕜) P).toLinearMap
    | some j => (MvPolynomial.aeval (R := 𝕜) P).toLinearMap.comp (MvPolynomial.pderiv j).toLinearMap)

lemma jetLinearMap_apply (r : ℕ) (P : Fin r → 𝕜) (f : MvPolynomial (Fin r) 𝕜) (k : Option (Fin r)) :
    jetLinearMap r P f k = MvPolynomial.eval P (Option.elim k f (fun j => MvPolynomial.pderiv j f)) := by
  cases k <;> simp [jetLinearMap]

noncomputable def pointsJetMap (r m : ℕ) (P : Fin m → (Fin r → 𝕜)) :
    MvPolynomial (Fin r) 𝕜 →ₗ[𝕜] (Fin m → Option (Fin r) → 𝕜) :=
  LinearMap.pi (fun i => jetLinearMap r (P i))

lemma pointsJetMap_apply (r m : ℕ) (P : Fin m → (Fin r → 𝕜)) (f : MvPolynomial (Fin r) 𝕜) (i : Fin m) :
    pointsJetMap r m P f i = jetLinearMap r (P i) f := by
  simp [pointsJetMap]

noncomputable def pointsJetMapBdd (r d m : ℕ) (P : Fin m → (Fin r → 𝕜)) :
    MvPolynomial.restrictTotalDegree (Fin r) 𝕜 d →ₗ[𝕜] (Fin m → Option (Fin r) → 𝕜) :=
  (pointsJetMap r m P).comp (MvPolynomial.restrictTotalDegree (Fin r) 𝕜 d).subtype

lemma pointsJetMapBdd_apply (r d m : ℕ) (P : Fin m → (Fin r → 𝕜))
    (x : MvPolynomial.restrictTotalDegree (Fin r) 𝕜 d) :
    pointsJetMapBdd r d m P x = pointsJetMap r m P (x : MvPolynomial (Fin r) 𝕜) := rfl

lemma finrank_jetsTarget (r m : ℕ) :
    Module.finrank 𝕜 (Fin m → Option (Fin r) → 𝕜) = m * (r + 1) := by
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_option, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

lemma surjective_pointsJetMapBdd_iff (r d m : ℕ) (P : Fin m → (Fin r → 𝕜)) :
    Function.Surjective (pointsJetMapBdd r d m P) ↔
      (∀ g : Fin m → Option (Fin r) → 𝕜, ∃ f : MvPolynomial (Fin r) 𝕜,
        f.totalDegree ≤ d ∧ pointsJetMap r m P f = g) := by
  constructor
  · intro h g
    obtain ⟨x, hx⟩ := h g
    exact ⟨x.1, (MvPolynomial.mem_restrictTotalDegree (Fin r) d x.1).mp x.2, hx⟩
  · intro h g
    obtain ⟨f, hf, hfg⟩ := h g
    exact ⟨⟨f, (MvPolynomial.mem_restrictTotalDegree (Fin r) d f).mpr hf⟩, hfg⟩

/-! ### Polynomial helpers -/

lemma totalDegree_X_sub_C_le (r : ℕ) (Q : Fin r → 𝕜) (j : Fin r) :
    (MvPolynomial.X j - MvPolynomial.C (Q j) : MvPolynomial (Fin r) 𝕜).totalDegree ≤ 1 := by
  have h : (MvPolynomial.X j - MvPolynomial.C (Q j) : MvPolynomial (Fin r) 𝕜)
      = MvPolynomial.X j + MvPolynomial.C (-(Q j)) := by
    rw [sub_eq_add_neg, ← MvPolynomial.C_neg]
  rw [h]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  exact max_le le_rfl zero_le

lemma pderiv_X_sub_C (r : ℕ) (Q : Fin r → 𝕜) (j k : Fin r) :
    (MvPolynomial.pderiv k) (MvPolynomial.X j - MvPolynomial.C (Q j) : MvPolynomial (Fin r) 𝕜)
      = (if j = k then 1 else 0) := by
  rw [map_sub, MvPolynomial.pderiv_C, sub_zero]
  by_cases h : j = k
  · subst h; rw [MvPolynomial.pderiv_X_self, if_pos rfl]
  · rw [MvPolynomial.pderiv_X_of_ne h, if_neg h]

lemma eval_X_sub_C_eq (r : ℕ) (v Q : Fin r → 𝕜) (j : Fin r) :
    MvPolynomial.eval v (MvPolynomial.X j - MvPolynomial.C (Q j) : MvPolynomial (Fin r) 𝕜)
      = v j - Q j := by
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]

lemma eval_pderiv_X_sub_C (r : ℕ) (v Q : Fin r → 𝕜) (j k : Fin r) :
    MvPolynomial.eval v ((MvPolynomial.pderiv k)
      (MvPolynomial.X j - MvPolynomial.C (Q j) : MvPolynomial (Fin r) 𝕜))
      = (if j = k then 1 else 0) := by
  rw [pderiv_X_sub_C]
  by_cases h : j = k <;> simp [h]

lemma jetLinearMap_X_sub_C_mul_none (r : ℕ) (Q : Fin r → 𝕜) (f : MvPolynomial (Fin r) 𝕜) (j : Fin r) :
    jetLinearMap r Q ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f) none = 0 := by
  rw [jetLinearMap_apply]
  simp only [Option.elim]
  rw [MvPolynomial.eval_mul, eval_X_sub_C_eq, sub_self, zero_mul]

lemma jetLinearMap_X_sub_C_mul_some (r : ℕ) (Q : Fin r → 𝕜) (f : MvPolynomial (Fin r) 𝕜)
    (j k : Fin r) :
    jetLinearMap r Q ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f) (some k)
      = (if j = k then MvPolynomial.eval Q f else 0) := by
  rw [jetLinearMap_apply]
  simp only [Option.elim]
  rw [MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
    eval_pderiv_X_sub_C, eval_X_sub_C_eq, sub_self, zero_mul, add_zero]
  by_cases h : j = k <;> simp [h]



lemma exists_jet_interpolant (r d m : ℕ) (hd : 1 ≤ d) (P : Fin m → (Fin r → 𝕜))
    (f₀ : MvPolynomial (Fin r) 𝕜) (hf₀deg : f₀.totalDegree ≤ d - 1)
    (hf₀ker : pointsJetMap r m P f₀ = 0) (Q : Fin r → 𝕜) (hc₀ : MvPolynomial.eval Q f₀ ≠ 0) :
    ∀ y : Option (Fin r) → 𝕜, ∃ h : MvPolynomial (Fin r) 𝕜,
      h.totalDegree ≤ d ∧ pointsJetMap r m P h = 0 ∧ jetLinearMap r Q h = y := by
  intro y
  have heval0 : ∀ i : Fin m, MvPolynomial.eval (P i) f₀ = 0 := by
    intro i
    have h1 : jetLinearMap r (P i) f₀ = 0 := by
      have := congr_fun hf₀ker i
      simpa [pointsJetMap_apply] using this
    have := congr_fun h1 none
    simpa [jetLinearMap_apply] using this
  have hevald0 : ∀ (i : Fin m) (j : Fin r),
      MvPolynomial.eval (P i) (MvPolynomial.pderiv j f₀) = 0 := by
    intro i j
    have h1 : jetLinearMap r (P i) f₀ = 0 := by
      have := congr_fun hf₀ker i
      simpa [pointsJetMap_apply] using this
    have := congr_fun h1 (some j)
    simpa [jetLinearMap_apply] using this
  have hPg : ∀ j : Fin r,
      pointsJetMap r m P ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f₀) = 0 := by
    intro j
    funext i k
    rcases k with _ | k
    · rw [pointsJetMap_apply, jetLinearMap_apply]
      simp only [Option.elim, MvPolynomial.eval_mul, eval_X_sub_C_eq, heval0 i, mul_zero,
        Pi.zero_apply]
    · rw [pointsJetMap_apply, jetLinearMap_apply]
      simp only [Option.elim, MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        eval_pderiv_X_sub_C, eval_X_sub_C_eq, heval0 i, hevald0 i k, mul_zero, add_zero,
        Pi.zero_apply]
  let v₀ : Option (Fin r) → 𝕜 := jetLinearMap r Q f₀
  have hv₀none : v₀ none = MvPolynomial.eval Q f₀ := by simp [v₀, jetLinearMap_apply]
  have hv₀some : ∀ j, v₀ (some j) = MvPolynomial.eval Q (MvPolynomial.pderiv j f₀) := by
    intro j; simp [v₀, jetLinearMap_apply]
  let a := y none / v₀ none
  let b : Fin r → 𝕜 := fun j => (y (some j) - a * v₀ (some j)) / v₀ none
  let h := a • f₀ + ∑ j : Fin r, b j • ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f₀)
  have ha : a = y none / v₀ none := rfl
  have hb : ∀ j, b j = (y (some j) - a * v₀ (some j)) / v₀ none := fun j => rfl
  have hvc : v₀ none ≠ 0 := by rw [hv₀none]; exact hc₀
  refine ⟨h, ?_, ?_, ?_⟩
  · -- degree
    have h1 : (a • f₀).totalDegree ≤ d :=
      le_trans (MvPolynomial.totalDegree_smul_le a f₀) (by omega)
    have h2 : (∑ j : Fin r, b j • ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f₀)).totalDegree ≤ d := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro j _
      refine le_trans (MvPolynomial.totalDegree_smul_le (b j) _) ?_
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h3 := totalDegree_X_sub_C_le r Q j
      omega
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le h1 h2)
  · -- pointsJetMap P h = 0
    have hsum : pointsJetMap r m P (∑ j : Fin r, b j • ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f₀)) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul, hPg j, smul_zero]
    simp only [h, map_add, map_smul, hf₀ker, smul_zero, hsum, add_zero]
  · -- jetLinearMap Q h = y
    have hjet : jetLinearMap r Q h = a • v₀
        + ∑ j : Fin r, b j • jetLinearMap r Q ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f₀) := by
      simp only [h, map_add, map_smul, map_sum, v₀]
    funext k
    rw [hjet]
    rcases k with _ | k
    · simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, jetLinearMap_X_sub_C_mul_none,
        mul_zero, Finset.sum_const_zero, add_zero, smul_eq_mul]
      rw [show a * v₀ none = y none from by rw [ha]; exact div_mul_cancel₀ _ hvc]
    · have hsum2 : (∑ j : Fin r, b j • jetLinearMap r Q ((MvPolynomial.X j - MvPolynomial.C (Q j)) * f₀)) (some k)
            = b k * v₀ none := by
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single k]
        · simp only [Pi.smul_apply, jetLinearMap_X_sub_C_mul_some, hv₀none, if_pos, smul_eq_mul]
        · intro j _ hj
          simp only [Pi.smul_apply, jetLinearMap_X_sub_C_mul_some, if_neg hj, mul_zero, smul_eq_mul]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      simp only [Pi.add_apply, Pi.smul_apply, hsum2, smul_eq_mul]
      rw [show b k * v₀ none = y (some k) - a * v₀ (some k) from by
        rw [hb k]; exact div_mul_cancel₀ _ hvc]
      ring


lemma pointsJetMapBdd_extend (r d m : ℕ) (hd : 1 ≤ d) (P : Fin m → (Fin r → 𝕜))
    (hsurj : Function.Surjective (pointsJetMapBdd r d m P))
    (hdim : m * (r + 1) < (d - 1 + r).choose r) :
    ∃ Q : Fin r → 𝕜, Function.Surjective (pointsJetMapBdd r d (m + 1) (Fin.snoc P Q)) := by
  classical
  let W := MvPolynomial.restrictTotalDegree (Fin r) 𝕜 (d - 1)
  let φ : W →ₗ[𝕜] (Fin m → Option (Fin r) → 𝕜) := (pointsJetMap r m P).comp W.subtype
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hWfin : Module.finrank 𝕜 W = (d - 1 + r).choose r := finrank_restrictTotalDegree 𝕜 r (d - 1)
  have htarget : Module.finrank 𝕜 (Fin m → Option (Fin r) → 𝕜) = m * (r + 1) := finrank_jetsTarget r m
  have hle : Module.finrank 𝕜 ↥(LinearMap.range φ) ≤ m * (r + 1) := by
    rw [← htarget]
    exact Submodule.finrank_le (LinearMap.range φ)
  have hpos : 0 < Module.finrank 𝕜 ↥(LinearMap.ker φ) := by
    rw [hWfin] at hrank
    omega
  haveI : Nontrivial ↥(LinearMap.ker φ) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : ↥(LinearMap.ker φ))
  let f₀ : MvPolynomial (Fin r) 𝕜 := x.1.1
  have hf₀deg : f₀.totalDegree ≤ d - 1 :=
    (MvPolynomial.mem_restrictTotalDegree (Fin r) (d - 1) f₀).mp x.1.2
  have hf₀ne : f₀ ≠ 0 := fun hh => hx (Subtype.ext (Subtype.ext hh))
  have hf₀ker : pointsJetMap r m P f₀ = 0 := by
    have h2 : φ x.1 = 0 := LinearMap.mem_ker.mp x.2
    rwa [show φ x.1 = pointsJetMap r m P f₀ from rfl] at h2
  obtain ⟨u, -, hu_ne⟩ :=
    exists_eval_ne_zero_of_totalDegree_le
      (F := 𝕜) f₀ hf₀ne hf₀deg
  let Q : Fin r → 𝕜 := fun i => (u i : 𝕜)
  have hc₀ : MvPolynomial.eval Q f₀ ≠ 0 := hu_ne
  refine ⟨Q, ?_⟩
  intro g
  let g' : Fin m → Option (Fin r) → 𝕜 := fun i => g (Fin.castSucc i)
  obtain ⟨x₀, hx₀⟩ := hsurj g'
  let y : Option (Fin r) → 𝕜 := g (Fin.last m) - jetLinearMap r Q (x₀ : MvPolynomial (Fin r) 𝕜)
  have hy : y = g (Fin.last m) - jetLinearMap r Q (x₀ : MvPolynomial (Fin r) 𝕜) := rfl
  obtain ⟨h₀, hh₀deg, hh₀ker, hh₀jet⟩ :=
    exists_jet_interpolant r d m hd P f₀ hf₀deg hf₀ker Q hc₀ y
  set f₁ : MvPolynomial.restrictTotalDegree (Fin r) 𝕜 d :=
    x₀ + ⟨h₀, (MvPolynomial.mem_restrictTotalDegree (Fin r) d h₀).mpr hh₀deg⟩ with hf₁
  refine ⟨f₁, ?_⟩
  have hf₁coe : (f₁ : MvPolynomial (Fin r) 𝕜) = (x₀ : MvPolynomial (Fin r) 𝕜) + h₀ := rfl
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [pointsJetMapBdd_apply, pointsJetMap_apply, Fin.snoc_last, hf₁coe, map_add, hh₀jet]
    rw [hy]
    abel
  · intro i'
    rw [pointsJetMapBdd_apply, pointsJetMap_apply, Fin.snoc_castSucc, hf₁coe, map_add]
    have h1 : jetLinearMap r (P i') (x₀ : MvPolynomial (Fin r) 𝕜) = g' i' := by
      rw [← pointsJetMap_apply, ← pointsJetMapBdd_apply]; exact congr_fun hx₀ i'
    have h2 : jetLinearMap r (P i') h₀ = 0 := by
      rw [← pointsJetMap_apply, hh₀ker]; rfl
    rw [h1, h2, add_zero]


lemma exists_pointsJetMapBdd_surjective (r d : ℕ) (hd : 1 ≤ d) (n : ℕ)
    (hcond : ∀ k < n, k * (r + 1) < (d - 1 + r).choose r) :
    ∃ P : Fin n → (Fin r → 𝕜), Function.Surjective (pointsJetMapBdd r d n P) := by
  induction n with
  | zero =>
      refine ⟨Fin.elim0, ?_⟩
      intro g
      exact ⟨0, Subsingleton.elim _ _⟩
  | succ k ih =>
      obtain ⟨P, hP⟩ := ih (fun j hj => hcond j (Nat.lt_succ_of_lt hj))
      obtain ⟨Q, hQ⟩ := pointsJetMapBdd_extend r d k hd P hP (hcond k (Nat.lt_succ_self k))
      exact ⟨Fin.snoc P Q, hQ⟩

theorem exists_points_eval_surjective (r d n : ℕ) (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜] (h : (n - 1) * (r + 1) < (d + r - 1).choose r) : ∃ P : Fin n → (Fin r → 𝕜), ∀ g : Fin n → (Option (Fin r) → 𝕜), ∃ f : MvPolynomial (Fin r) 𝕜, f.totalDegree ≤ d ∧ ∀ i : Fin n, ∀ k : Option (Fin r), MvPolynomial.eval (P i) (Option.elim k f (fun j => MvPolynomial.pderiv j f)) = g i k := by

  by_cases hr : r = 0
  · subst hr
    have hn : n ≤ 1 := by
      have h1 := h
      simp only [Nat.choose_zero_right] at h1
      omega
    interval_cases n
    · refine ⟨Fin.elim0, ?_⟩
      intro g
      exact ⟨0, by simp, by intro i; exact i.elim0⟩
    · refine ⟨fun (_ : Fin 1) => Fin.elim0, ?_⟩
      intro g
      refine ⟨MvPolynomial.C (g 0 none), by simp, ?_⟩
      intro i k
      have hi : i = 0 := Subsingleton.elim i 0
      have hk : k = none := Subsingleton.elim k none
      rw [hi, hk]
      simp
  · by_cases hd : 1 ≤ d
    · have hdr : d - 1 + r = d + r - 1 := by omega
      have hcond : ∀ k < n, k * (r + 1) < (d - 1 + r).choose r := by
        intro k hk
        have hkn : k ≤ n - 1 := by omega
        have h1 : k * (r + 1) ≤ (n - 1) * (r + 1) := Nat.mul_le_mul_right _ hkn
        rw [hdr]
        exact lt_of_le_of_lt h1 h
      obtain ⟨P, hP⟩ := exists_pointsJetMapBdd_surjective (𝕜 := 𝕜) r d hd n hcond
      rw [surjective_pointsJetMapBdd_iff] at hP
      refine ⟨P, ?_⟩
      intro g
      obtain ⟨f, hf, hfg⟩ := hP g
      refine ⟨f, hf, ?_⟩
      intro i k
      have := congr_fun (congr_fun hfg i) k
      rwa [pointsJetMap_apply, jetLinearMap_apply] at this
    · exfalso
      have hd0 : d = 0 := by omega
      subst hd0
      have hlt : (r - 1) < r := by omega
      have hz : (0 + r - 1).choose r = 0 := by
        rw [show 0 + r - 1 = r - 1 from by omega, Nat.choose_eq_zero_of_lt hlt]
      rw [hz] at h
      omega

end Commons.Algebra.MvPolynomial