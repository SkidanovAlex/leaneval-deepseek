import Mathlib
import Submission.Work.Peluse.UControl.petStepDefs
import Submission.Work.Peluse.PET.pet_step

namespace Work.Peluse.UControl

/-! ## Helper lemmas

The averaged PET step is the Cauchy–Schwarz/Jensen average over the parameter set `Ω` of the
single-parameter PET step, so the only new ingredients are the single-parameter step and two
product-reindexing identities.  The single-parameter step needs Peluse's PET step
(`Work.Peluse.PET.pet_step`) for the *arbitrary* index type `ι : Type*` of the averaged statement,
whereas `pet_step` is stated at universe level `0`; `petStepUniv` is the same statement with the
index type at an arbitrary universe, obtained from `pet_step` at `Fin (Fintype.card ι)` by
transporting the family along `Fintype.equivFin`.-/

/-- The product over all slots except `(i₀, false)`, written as the product over `ι × Bool` with
the `(i₀, false)`-slot contributing `1`. -/
private lemma prod_compl_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (G : ι × Bool → ℂ) :
    (∏ j : {j : ι × Bool // j ≠ (i₀, false)}, G j.1)
      = ∏ i : ι, ∏ ε : Bool, (if ((i, ε) = (i₀, false)) then 1 else G (i, ε)) := by
  have h1 : (∏ i : ι, ∏ ε : Bool, (if ((i, ε) = (i₀, false)) then 1 else G (i, ε)))
      = ∏ p : ι × Bool, (if (p = (i₀, false)) then 1 else G p) :=
    (Fintype.prod_prod_type (fun p : ι × Bool => if p = (i₀, false) then 1 else G p)).symm
  have h3 : (∏ p : ι × Bool, (if (p = (i₀, false)) then 1 else G p))
      = ∏ p ∈ (Finset.univ : Finset (ι × Bool)).filter (fun p => p ≠ (i₀, false)), G p := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases h : p = (i₀, false) <;> simp [h]
  have h4 : (∏ p ∈ (Finset.univ : Finset (ι × Bool)).filter (fun p => p ≠ (i₀, false)), G p)
      = ∏ j : {j : ι × Bool // j ≠ (i₀, false)}, G j.1 :=
    Finset.prod_subtype _ (fun x => by simp) G
  rw [← h4, ← h3, ← h1]

/-- Reindexing a double product over a `Bool`-extended type along an equivalence. -/
private lemma prod_prod_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (Φ : ι × Bool → ℂ) (Φ' : ι' × Bool → ℂ) (h : ∀ i ε, Φ' (e i, ε) = Φ (i, ε)) :
    (∏ i : ι, ∏ ε : Bool, Φ (i, ε)) = ∏ i' : ι', ∏ ε : Bool, Φ' (i', ε) := by
  rw [← Fintype.prod_prod_type Φ, ← Fintype.prod_prod_type Φ']
  refine Fintype.prod_equiv (e.prodCongr (Equiv.refl Bool)) _ _ ?_
  intro p
  obtain ⟨i, ε⟩ := p
  exact (h i ε).symm

/-- **The PET step for an arbitrary index universe.**  This is `Work.Peluse.PET.pet_step` with the
index type `ι` at an arbitrary universe (the original is universe-monomorphic at `Type 0`).  The
proof transports the configuration along `Fintype.equivFin ι : ι ≃ Fin (Fintype.card ι)` and
applies `pet_step` at `Fin _`. -/
private lemma petStepUniv {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {N M : ℕ} (Cne : ℕ)
    {γ γ' : ℝ} (Q : ι → ℤ → ℤ) (f : ℤ → ℂ) (F : ι → ℤ → ℂ)
    (hN : 0 < N) (hM : 0 < M) (hγ : 0 < γ) (hγ' : 0 < γ')
    (hγ'γ : γ' ≤ γ / (1000 * ((Cne : ℝ) + 1)))
    (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hfs : Work.Peluse.SupportIn f N)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hQ : ∀ i, ∀ y ∈ Finset.Icc 1 M, |Q i (y : ℤ)| ≤ (Cne : ℤ) * (N : ℤ))
    (hLam : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i (y : ℤ))‖ ^ 2) :
    γ / 1000 ≤ ∑ a ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋.toNat : ℤ),
        Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat a *
          ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F i₀ x *
            ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, ∏ ε : Bool,
              (if ((i, ε) = (i₀, false)) then 1 else
                (if ε then star (F i (x + (Q i ((y : ℤ) + a) - Q i₀ (y : ℤ))))
                        else F i (x + (Q i (y : ℤ) - Q i₀ (y : ℤ)))))‖ := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set Q' : Fin (Fintype.card ι) → ℤ → ℤ := fun i' => Q (e.symm i') with hQ'def
  set F' : Fin (Fintype.card ι) → ℤ → ℂ := fun i' => F (e.symm i') with hF'def
  set i₀' : Fin (Fintype.card ι) := e i₀ with hi₀'def
  have hprod : ∀ x y : ℤ, (∏ i : ι, F i (x + Q i y))
      = ∏ i' : Fin (Fintype.card ι), F' i' (x + Q' i' y) := by
    intro x y
    refine Fintype.prod_equiv e _ _ fun i => ?_
    simp [hF'def, hQ'def]
  have hLS : (∑' x : ℤ, f x * ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i (y : ℤ)))
      = (∑' x : ℤ, f x * ∑ y ∈ Finset.Icc 1 M,
          ∏ i' : Fin (Fintype.card ι), F' i' (x + Q' i' (y : ℤ))) := by
    refine tsum_congr fun x => ?_
    congr 1
    exact Finset.sum_congr rfl fun y _ => hprod x (y : ℤ)
  have hLam' : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
      ∑ y ∈ Finset.Icc 1 M, ∏ i' : Fin (Fintype.card ι), F' i' (x + Q' i' (y : ℤ))‖ ^ 2 := by
    rw [← hLS]; exact hLam
  have hmain := Work.Peluse.PET.pet_step (ι := Fin (Fintype.card ι)) i₀' (Cne := Cne)
      (γ := γ) (γ' := γ') (Q := Q') (f := f) (F := F') hN hM hγ hγ' hγ'γ hH hf hfs
      (fun i' x => hF (e.symm i') x) (fun i' => hFs (e.symm i'))
      (fun i' y hy => hQ (e.symm i') y hy) hLam'
  have hRHS : (∑ a ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋).toNat,
        Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat a *
          ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F' i₀' x *
            ∑ y ∈ Finset.Icc 1 M, ∏ i' : Fin (Fintype.card ι), ∏ ε : Bool,
              (if ((i', ε) = (i₀', false)) then 1 else
                (if ε then star (F' i' (x + (Q' i' ((y : ℤ) + a) - Q' i₀' (y : ℤ))))
                        else F' i' (x + (Q' i' (y : ℤ) - Q' i₀' (y : ℤ)))))‖)
      = (∑ a ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋).toNat,
        Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat a *
          ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F i₀ x *
            ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, ∏ ε : Bool,
              (if ((i, ε) = (i₀, false)) then 1 else
                (if ε then star (F i (x + (Q i ((y : ℤ) + a) - Q i₀ (y : ℤ))))
                        else F i (x + (Q i (y : ℤ) - Q i₀ (y : ℤ)))))‖) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine congrArg (fun z => Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat a * z) ?_
    refine congrArg (fun z => ‖z‖) ?_
    refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
    refine tsum_congr fun x => ?_
    rw [show F' i₀' x = F i₀ x by simp [hF'def, hi₀'def]]
    refine congrArg (fun z => F i₀ x * z) ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    exact (prod_prod_comp_equiv e
      (fun p : ι × Bool => if (p = (i₀, false)) then 1 else
        (if p.2 then star (F p.1 (x + (Q p.1 ((y : ℤ) + a) - Q i₀ (y : ℤ))))
                  else F p.1 (x + (Q p.1 (y : ℤ) - Q i₀ (y : ℤ)))))
      (fun p : Fin (Fintype.card ι) × Bool => if (p = (i₀', false)) then 1 else
        (if p.2 then star (F' p.1 (x + (Q' p.1 ((y : ℤ) + a) - Q' i₀' (y : ℤ))))
                  else F' p.1 (x + (Q' p.1 (y : ℤ) - Q' i₀' (y : ℤ)))))
      (fun i ε => by simp [hF'def, hQ'def, hi₀'def])).symm
  calc γ / 1000 ≤ _ := hmain
    _ = _ := hRHS

/-- **The single-parameter PET step in the vocabulary of `PetStep`.**  This is Peluse's Lemma 4.2
for one parameter `a : Ω`: it is `petStepUniv` applied to the configuration `(fun i => Q i a, f, F)`
with `γ = ‖Λ_a‖²`, followed by the reindexing of the product over the `(i₀, false)`-slot
(`prod_compl_equiv`). -/
private lemma petStepPerParam {Ω ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {N M : ℕ}
    (Cne : ℕ) {γ' : ℝ} (Q : ι → Ω → ℤ → ℤ) (f : ℤ → ℂ) (F : ι → ℤ → ℂ) (a : Ω)
    (hN : 0 < N) (hM : 0 < M) (hγ' : 0 < γ')
    (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hfs : Work.Peluse.SupportIn f N)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hQ : ∀ i, ∀ y ∈ Finset.Icc 1 M, |Q i a (y : ℤ)| ≤ (Cne : ℤ) * (N : ℤ))
    (hpos : 0 < ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i a (y : ℤ))‖ ^ 2)
    (hγ'γ : γ' ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i a (y : ℤ))‖ ^ 2
          / (1000 * ((Cne : ℝ) + 1))) :
    ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i a (y : ℤ))‖ ^ 2 / 1000 ≤
      ∑ h ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋.toNat : ℤ)) (⌊γ' * (M : ℝ)⌋).toNat,
        Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat h *
          ‖((N : ℂ) * (M : ℂ))⁻¹ *
            ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x *
              ∑ y ∈ Finset.Icc 1 M,
                ∏ j : {j : ι × Bool // j ≠ (i₀, false)},
                  Work.Peluse.UControl.PetStep.stepF F j.1
                    (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ))‖ := by
  classical
  have hmain := petStepUniv (ι := ι) i₀ (Cne := Cne)
    (γ := ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i a (y : ℤ))‖ ^ 2) (γ' := γ')
    (Q := fun i => Q i a) (f := f) (F := F) hN hM hpos hγ' hγ'γ hH hf hfs hF hFs
    (fun i => hQ i) (le_refl _)
  refine le_trans hmain ?_
  refine le_of_eq ?_
  refine Finset.sum_congr rfl fun h _ => ?_
  refine congrArg (fun z => Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat h * z) ?_
  refine congrArg (fun z => ‖z‖) ?_
  refine congrArg (fun z => ((N : ℂ) * (M : ℂ))⁻¹ * z) ?_
  refine tsum_congr fun x => ?_
  rw [show Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x = F i₀ x from rfl]
  refine congrArg (fun z => F i₀ x * z) ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  set G : ι × Bool → ℂ := fun p => Work.Peluse.UControl.PetStep.stepF F p
    (x + (if p.2 then Q p.1 a ((y : ℤ) + h) - Q i₀ a (y : ℤ)
          else Q p.1 a (y : ℤ) - Q i₀ a (y : ℤ))) with hGdef
  have hsub : (∏ j : {j : ι × Bool // j ≠ (i₀, false)},
        Work.Peluse.UControl.PetStep.stepF F j.1
          (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ)))
      = ∏ j : {j : ι × Bool // j ≠ (i₀, false)}, G j.1 :=
    Finset.prod_congr rfl fun j _ => by simp [hGdef, Work.Peluse.UControl.PetStep.stepQ]
  rw [hsub, prod_compl_equiv i₀ G]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun ε _ => ?_
  by_cases hc : ((i, ε) = (i₀, false))
  · simp [hc]
  · simp only [hc, if_false]
    cases ε <;> simp [hGdef, Work.Peluse.UControl.PetStep.stepF]

theorem petStepAvgRepair {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {N M : ℕ} (Cne : ℕ) {γ γ' : ℝ}
    (Q : ι → Ω → ℤ → ℤ) (f : Ω → ℤ → ℂ) (F : ι → ℤ → ℂ) (ν : Ω → ℝ)
    (hN : 0 < N) (hM : 0 < M) (hγ : 0 < γ) (hγ' : 0 < γ')
    (hν0 : ∀ a, 0 ≤ ν a) (hν1 : ∑ a, ν a = 1)
    (hγ'γ : γ' ≤ γ ^ 2 / (20000 * ((Cne : ℝ) + 1)))
    (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hf : ∀ a x, ‖f a x‖ ≤ 1) (hfs : ∀ a, Work.Peluse.SupportIn (f a) N)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hQ : ∀ i a, ∀ y ∈ Finset.Icc 1 M, |Q i a (y : ℤ)| ≤ (Cne : ℤ) * (N : ℤ))
    (hLam : γ ≤ ∑ a, ν a * ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f a x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i a (y : ℤ))‖) :
    γ ^ 2 / 2000 ≤ ∑ a, ν a *
      ∑ h ∈ Finset.Icc (-(⌊γ' * (M : ℝ)⌋).toNat : ℤ) (⌊γ' * (M : ℝ)⌋).toNat,
        Work.Peluse.muL ⌊γ' * (M : ℝ)⌋.toNat h *
          ‖((N : ℂ) * (M : ℂ))⁻¹ *
            ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x *
              ∑ y ∈ Finset.Icc 1 M,
                ∏ j : {j : ι × Bool // j ≠ (i₀, false)},
                  Work.Peluse.UControl.PetStep.stepF F j.1
                    (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ))‖ := by
  classical
  let H : ℕ := ⌊γ' * (M : ℝ)⌋.toNat
  let Λ : Ω → ℂ := fun a => ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f a x *
    ∑ y ∈ Finset.Icc 1 M, ∏ i : ι, F i (x + Q i a (y : ℤ))
  let X : Ω → ℝ := fun a => ‖Λ a‖ ^ 2
  -- ## Step 1: Jensen (Cauchy–Schwarz in the parameter `a`)
  have hjensen : γ ^ 2 ≤ ∑ a, ν a * X a := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Ω)
      (fun a => Real.sqrt (ν a)) (fun a => Real.sqrt (ν a) * ‖Λ a‖)
    have h1 : ∑ a, Real.sqrt (ν a) * (Real.sqrt (ν a) * ‖Λ a‖) = ∑ a, ν a * ‖Λ a‖ := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (hν0 a)]
    have h2 : ∑ a, (Real.sqrt (ν a)) ^ 2 = ∑ a, ν a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Real.sq_sqrt (hν0 a)]
    have h3 : ∑ a, (Real.sqrt (ν a) * ‖Λ a‖) ^ 2 = ∑ a, ν a * X a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [X]
      rw [mul_pow, Real.sq_sqrt (hν0 a)]
    calc γ ^ 2 ≤ (∑ a, ν a * ‖Λ a‖) ^ 2 := pow_le_pow_left₀ (le_of_lt hγ) hLam 2
      _ = (∑ a, Real.sqrt (ν a) * (Real.sqrt (ν a) * ‖Λ a‖)) ^ 2 := by rw [h1]
      _ ≤ (∑ a, (Real.sqrt (ν a)) ^ 2) * ∑ a, (Real.sqrt (ν a) * ‖Λ a‖) ^ 2 := hcs
      _ = 1 * ∑ a, ν a * X a := by rw [h2, hν1, h3]
      _ = ∑ a, ν a * X a := by rw [one_mul]
  -- ## Step 2: the bad parameters carry at most `γ²/18` of the mass
  have hbad : ∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => ¬ (γ ^ 2 / 18 ≤ X a)), ν a * X a
      ≤ γ ^ 2 / 18 := by
    have hterm : ∀ a ∈ (Finset.univ : Finset Ω).filter (fun a => ¬ (γ ^ 2 / 18 ≤ X a)),
        ν a * X a ≤ ν a * (γ ^ 2 / 18) := by
      intro a ha
      exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp ha).2))
        (hν0 a)
    calc ∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => ¬ (γ ^ 2 / 18 ≤ X a)), ν a * X a
        ≤ ∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => ¬ (γ ^ 2 / 18 ≤ X a)),
            ν a * (γ ^ 2 / 18) := Finset.sum_le_sum hterm
      _ = (∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => ¬ (γ ^ 2 / 18 ≤ X a)), ν a)
            * (γ ^ 2 / 18) := by rw [Finset.sum_mul]
      _ ≤ (∑ a, ν a) * (γ ^ 2 / 18) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun a _ _ => hν0 a)
      _ = γ ^ 2 / 18 := by rw [hν1, one_mul]
  -- ## Step 3: the good parameters carry at least `γ²/2`
  have hgood : γ ^ 2 / 2 ≤ ∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => γ ^ 2 / 18 ≤ X a),
      ν a * X a := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset Ω))
      (p := fun a => γ ^ 2 / 18 ≤ X a) (f := fun a => ν a * X a)
    have hγ2 : (0 : ℝ) ≤ γ ^ 2 := sq_nonneg γ
    linarith [hsplit, hjensen, hbad, hγ2]
  -- ## Step 4: the single-parameter PET step at every good parameter
  have hkey : ∀ a ∈ (Finset.univ : Finset Ω).filter (fun a => γ ^ 2 / 18 ≤ X a),
      X a / 1000 ≤ ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H h *
        ‖((N : ℂ) * (M : ℂ))⁻¹ *
          ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x *
            ∑ y ∈ Finset.Icc 1 M,
              ∏ j : {j : ι × Bool // j ≠ (i₀, false)},
                Work.Peluse.UControl.PetStep.stepF F j.1
                  (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ))‖ := by
    intro a ha
    have hXge : γ ^ 2 / 18 ≤ X a := (Finset.mem_filter.mp ha).2
    have hXpos : 0 < X a := by
      have : 0 < γ ^ 2 / 18 := by positivity
      linarith
    have hγ'γa : γ' ≤ X a / (1000 * ((Cne : ℝ) + 1)) := by
      have hk : (0 : ℝ) < 1000 * ((Cne : ℝ) + 1) := by positivity
      have hc : (0 : ℝ) < (Cne : ℝ) + 1 := by positivity
      have h20 : γ ^ 2 ≤ 20 * X a := by linarith
      have h1 : γ' * (20000 * ((Cne : ℝ) + 1)) ≤ γ ^ 2 := by
        rw [le_div_iff₀ (by positivity)] at hγ'γ
        exact hγ'γ
      rw [le_div_iff₀ hk]
      nlinarith [h1, h20, hc]
    have hmain := petStepPerParam (Ω := Ω) (ι := ι) i₀ (N := N) (M := M) (Cne := Cne)
      (γ' := γ') (Q := Q) (f := f a) (F := F) (a := a) hN hM hγ' hH (hf a) (hfs a) hF hFs
      (fun i => hQ i a) (by simpa only [X, Λ] using hXpos) (by simpa only [X, Λ] using hγ'γa)
    simpa only [H, X, Λ] using hmain
  -- ## Step 5: assemble
  have hgoodSum : γ ^ 2 / 2000 ≤
      ∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => γ ^ 2 / 18 ≤ X a), ν a *
        ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H h *
          ‖((N : ℂ) * (M : ℂ))⁻¹ *
            ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x *
              ∑ y ∈ Finset.Icc 1 M,
                ∏ j : {j : ι × Bool // j ≠ (i₀, false)},
                  Work.Peluse.UControl.PetStep.stepF F j.1
                    (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ))‖ := by
    have h1 : (∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => γ ^ 2 / 18 ≤ X a), ν a * X a)
          / 1000 ≤ ∑ a ∈ (Finset.univ : Finset Ω).filter (fun a => γ ^ 2 / 18 ≤ X a), ν a *
          (∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H h *
            ‖((N : ℂ) * (M : ℂ))⁻¹ *
              ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x *
                ∑ y ∈ Finset.Icc 1 M,
                  ∏ j : {j : ι × Bool // j ≠ (i₀, false)},
                    Work.Peluse.UControl.PetStep.stepF F j.1
                      (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ))‖) := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun a ha => ?_
      calc ν a * X a / 1000 = ν a * (X a / 1000) := by ring
        _ ≤ ν a * _ := mul_le_mul_of_nonneg_left (hkey a ha) (hν0 a)
    have h2 : γ ^ 2 / 2000 ≤ (∑ a ∈ (Finset.univ : Finset Ω).filter
        (fun a => γ ^ 2 / 18 ≤ X a), ν a * X a) / 1000 := by
      linarith [hgood]
    linarith [h1, h2]
  have hgoal : γ ^ 2 / 2000 ≤ ∑ a, ν a *
      ∑ h ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H h *
        ‖((N : ℂ) * (M : ℂ))⁻¹ *
          ∑' x : ℤ, Work.Peluse.UControl.PetStep.stepBase F i₀ (a, h) x *
            ∑ y ∈ Finset.Icc 1 M,
              ∏ j : {j : ι × Bool // j ≠ (i₀, false)},
                Work.Peluse.UControl.PetStep.stepF F j.1
                  (x + Work.Peluse.UControl.PetStep.stepQ Q i₀ j (a, h) (y : ℤ))‖ := by
    refine le_trans hgoodSum ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => mul_nonneg (hν0 a) (Finset.sum_nonneg fun h _ =>
        mul_nonneg (Work.Peluse.PET.muL_nonneg H h) (norm_nonneg _)))
  exact hgoal


end Work.Peluse.UControl
