import Mathlib
import Submission.Work.Peluse.Prop36SW.GenDefs
import Submission.Work.Peluse.LadderA.boxNormPow_level_raise
import Submission.Work.Peluse.BoxNorm.boxNormPow_perm
import Submission.Work.Prop36SW.exists_perm_castSucc_factor
import Submission.Work.Prop36SW.boxNorm_le_of_boxNormPow_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Prop36SW

/-- **Monotonicity of the box-norm power in the direction family.**

If `Q'` is a direction family at level `n` whose directions contain those of a family `Q` at level
`t ≤ n` (in the sense that `Q = Q' ∘ e` for an injection `e : Fin t ↪ Fin n`), then the level-`t`
box-norm power of a function supported in `symIcc N` is bounded by the level-`n` power:

`(‖f‖^{2^t}_{□^t_Q}) ^ {2^{n-t}} ≤ 2^{2^{n-t}-1} · ‖f‖^{2^n}_{□^n_{Q'}}`.

Proved by induction on `n`: the extra directions are appended one at a time via the
Gowers–Cauchy–Schwarz step `two_mul_boxNormPow_succ_ge_complex`, the injection `e` being pushed
into the image of `Fin.castSucc` by a permutation of the index set (which leaves the box-norm power
unchanged, `boxNormPow_perm`). -/
theorem boxNormPow_le_of_inj {N : ℕ} (hN : 0 < N) (f : ℤ → ℂ)
    (hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0) :
    ∀ (n : ℕ) (t : ℕ), t ≤ n → ∀ (Q : Fin t → Finset ℤ) (Q' : Fin n → Finset ℤ)
      (e : Fin t ↪ Fin n),
      (∀ i, Q' (e i) = Q i) →
      (∀ i, (Q' i).Nonempty) →
      (∀ i z, z ∈ Q' i → |z| ≤ (N : ℤ)) →
      (Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc N) f) ^ (2 ^ (n - t))
        ≤ (2 : ℝ) ^ (2 ^ (n - t) - 1) * Work.Peluse.boxNormPow n Q' (Work.Peluse.symIcc N) f := by
  intro n
  induction n with
  | zero =>
      intro t ht Q Q' e he hne hbd
      obtain rfl : t = 0 := Nat.eq_zero_of_le_zero ht
      have hQQ' : Q = Q' := by funext j; exact Fin.elim0 j
      rw [hQQ']
      simp
  | succ n ih =>
      intro t ht Q Q' e he hne hbd
      rcases Nat.lt_or_ge t (n + 1) with hlt | hge
      · have htn : t ≤ n := Nat.lt_succ_iff.mp hlt
        obtain ⟨τ, e', hτ⟩ := exists_perm_castSucc_factor htn e
        set Q₂ : Fin (n + 1) → Finset ℤ := fun i => Q' (τ.symm i) with hQ₂
        have he' : ∀ i : Fin t, (fun j : Fin n => Q₂ (Fin.castSucc j)) (e' i) = Q i := by
          intro i
          rw [hQ₂]
          show Q' (τ.symm (Fin.castSucc (e' i))) = Q i
          rw [← hτ i, Equiv.symm_apply_apply, he i]
        have hne' : ∀ j : Fin n, ((fun j : Fin n => Q₂ (Fin.castSucc j)) j).Nonempty := by
          intro j
          rw [hQ₂]
          exact hne (τ.symm (Fin.castSucc j))
        have hbd' : ∀ j : Fin n, ∀ z, z ∈ (fun j : Fin n => Q₂ (Fin.castSucc j)) j →
            |z| ≤ (N : ℤ) := by
          intro j z hz
          rw [hQ₂] at hz
          exact hbd (τ.symm (Fin.castSucc j)) z hz
        have hIH := ih t htn Q (fun j : Fin n => Q₂ (Fin.castSucc j)) e' he' hne' hbd'
        have hne₂ : ∀ i : Fin (n + 1), (Q₂ i).Nonempty := by
          intro i
          rw [hQ₂]
          exact hne (τ.symm i)
        have hbd₂ : ∀ a ∈ Q₂ (Fin.last n), |a| ≤ (N : ℤ) := by
          intro a ha
          rw [hQ₂] at ha
          exact hbd (τ.symm (Fin.last n)) a ha
        have hstep :=
          Work.Peluse.Concat.two_mul_boxNormPow_succ_ge_complex Q₂ hN f hne₂ hbd₂ hsup
        have hperm : Work.Peluse.boxNormPow (n + 1) Q₂ (Work.Peluse.symIcc N) f
            = Work.Peluse.boxNormPow (n + 1) Q' (Work.Peluse.symIcc N) f := by
          rw [hQ₂]
          exact Work.Peluse.BoxNorm.boxNormPow_perm τ.symm Q' (Work.Peluse.symIcc N) f
        rw [← hperm]
        -- the arithmetic of the exponents
        set X : ℝ := Work.Peluse.boxNormPow t Q (Work.Peluse.symIcc N) f with hX
        set Y : ℝ := Work.Peluse.boxNormPow n (fun j : Fin n => Q₂ (Fin.castSucc j))
          (Work.Peluse.symIcc N) f with hY
        set Z : ℝ := Work.Peluse.boxNormPow (n + 1) Q₂ (Work.Peluse.symIcc N) f with hZ
        have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
        have hY0 : 0 ≤ Y := by rw [hY]; exact norm_nonneg _
        have hZ0 : 0 ≤ Z := by rw [hZ]; exact norm_nonneg _
        have hb1 : n + 1 - t = n - t + 1 := by omega
        have hb2 : 2 ^ (n + 1 - t) = 2 * 2 ^ (n - t) := by rw [hb1, pow_succ]; ring
        have hb3 : 2 ^ (n + 1 - t) - 1 = 2 * (2 ^ (n - t) - 1) + 1 := by
          rw [hb1, pow_succ]
          have h1 : 1 ≤ 2 ^ (n - t) := Nat.one_le_two_pow
          omega
        have hnat : 2 ^ (2 * (2 ^ (n - t) - 1) + 1) ≤ 2 ^ (2 ^ (n + 1 - t) - 1) := by
          apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
          rw [hb3]
        have hIH' : X ^ (2 ^ (n - t)) ≤ 2 ^ (2 ^ (n - t) - 1) * Y := hIH
        have hstep' : Y ^ 2 ≤ 2 * Z := hstep
        calc X ^ (2 ^ (n + 1 - t))
            = (X ^ (2 ^ (n - t))) ^ 2 := by rw [hb2, mul_comm, ← pow_mul]
          _ ≤ (2 ^ (2 ^ (n - t) - 1) * Y) ^ 2 := by
              exact pow_le_pow_left₀ (pow_nonneg hX0 _) hIH' 2
          _ = (2 ^ (2 ^ (n - t) - 1)) ^ 2 * Y ^ 2 := by ring
          _ ≤ (2 ^ (2 ^ (n - t) - 1)) ^ 2 * (2 * Z) := by
              apply mul_le_mul_of_nonneg_left hstep'
              positivity
          _ = 2 ^ (2 * (2 ^ (n - t) - 1) + 1) * Z := by
              rw [← pow_mul, ← mul_assoc, ← pow_succ, mul_comm (2 ^ (n - t) - 1) 2]
          _ ≤ 2 ^ (2 ^ (n + 1 - t) - 1) * Z := by
              apply mul_le_mul_of_nonneg_right _ hZ0
              exact_mod_cast hnat
      · have hteq : t = n + 1 := le_antisymm ht hge
        subst hteq
        have hinj : Function.Injective (fun i : Fin (n + 1) => e i) := fun a b h => e.injective h
        have hbij : Function.Bijective (fun i : Fin (n + 1) => e i) :=
          ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
        set σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective (fun i : Fin (n + 1) => e i) hbij
          with hσ
        have hfam : (fun i : Fin (n + 1) => Q' (σ i)) = Q := by
          funext i
          rw [hσ, Equiv.ofBijective_apply]
          exact he i
        have heq : Work.Peluse.boxNormPow (n + 1) Q (Work.Peluse.symIcc N) f
            = Work.Peluse.boxNormPow (n + 1) Q' (Work.Peluse.symIcc N) f := by
          rw [← hfam]
          exact Work.Peluse.BoxNorm.boxNormPow_perm σ Q' (Work.Peluse.symIcc N) f
        rw [heq]
        simp

theorem boxNorm_famIdx_le_of_le {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (kω kω' : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (hle : ∀ ω, kω ω ≤ kω' ω)
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ N : ℕ) (a : Fin n → ℤ)
    (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ)
    (f : ℤ → ℂ) (hN : 0 < N)
    (hne : ∀ j : Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω')),
      ((fun j => Work.Peluse.Prop36SW.pDirFamG (kω := kω') p M₁ a b
        ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).symm j)) j).Nonempty)
    (hbd : ∀ j : Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω')), ∀ z,
      z ∈ (Work.Peluse.Prop36SW.pDirFamG (kω := kω') p M₁ a b
        ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).symm j)) → |z| ≤ (N : ℤ))
    (hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0) :
    Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx kω))
      (fun j => Work.Peluse.Prop36SW.pDirFamG (kω := kω) p M₁ a b
        ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j))
      (Work.Peluse.symIcc N) f
    ≤ 2 * Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx kω'))
        (fun j => Work.Peluse.Prop36SW.pDirFamG (kω := kω') p M₁ a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).symm j))
        (Work.Peluse.symIcc N) f
:= by
  classical
  -- the level comparison
  have htij : Fintype.card (Work.Peluse.UControl.FamIdx kω)
      ≤ Fintype.card (Work.Peluse.UControl.FamIdx kω') := by
    simp only [Work.Peluse.UControl.FamIdx, Fintype.card_sigma, Fintype.card_fin]
    exact Finset.sum_le_sum (fun ω _ => hle ω)
  -- the natural injection on the family index sets
  let ef : Work.Peluse.UControl.FamIdx kω → Work.Peluse.UControl.FamIdx kω' :=
    fun x => ⟨x.1, Fin.castLE (hle x.1) x.2⟩
  have hef : Function.Injective ef := by
    rintro ⟨ω, r⟩ ⟨ω', r'⟩ h
    simp only [ef] at h
    have h1 : ω = ω' := congrArg Sigma.fst h
    subst h1
    have hval : (Fin.castLE (hle ω) r).val = (Fin.castLE (hle ω) r').val :=
      congrArg (fun x => (x.2 : Fin (kω' x.1)).val) h
    have h3 : r = r' := Fin.ext (by simpa using hval)
    subst h3
    rfl
  let e : Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω)) ↪
      Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω')) :=
    ⟨fun i => Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')
        (ef ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm i)),
      by
        intro i j hij
        have h1 : ef ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm i)
            = ef ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j) :=
          (Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).injective hij
        exact (Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm.injective (hef h1)⟩
  have he : ∀ i : Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω)),
      (fun j => Work.Peluse.Prop36SW.pDirFamG (kω := kω') p M₁ a b
        ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).symm j)) (e i)
      = (fun j => Work.Peluse.Prop36SW.pDirFamG (kω := kω) p M₁ a b
        ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j)) i := by
    intro i
    show Work.Peluse.Prop36SW.pDirFamG (kω := kω') p M₁ a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).symm
            (Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')
              (ef ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm i))))
        = Work.Peluse.Prop36SW.pDirFamG (kω := kω) p M₁ a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm i)
    rw [Equiv.symm_apply_apply]
    show Work.Peluse.Prop36SW.pDirG p M₁ a b
          (ef ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm i)).1
        = Work.Peluse.Prop36SW.pDirG p M₁ a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm i).1
    rfl
  have hpow := boxNormPow_le_of_inj hN f hsup
    (Fintype.card (Work.Peluse.UControl.FamIdx kω'))
    (Fintype.card (Work.Peluse.UControl.FamIdx kω)) htij
    (fun j => Work.Peluse.Prop36SW.pDirFamG (kω := kω) p M₁ a b
      ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j))
    (fun j => Work.Peluse.Prop36SW.pDirFamG (kω := kω') p M₁ a b
      ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).symm j))
    e he hne hbd
  exact boxNorm_le_of_boxNormPow_le htij _ _ (Work.Peluse.symIcc N) f hpow

end Work.Prop36SW
