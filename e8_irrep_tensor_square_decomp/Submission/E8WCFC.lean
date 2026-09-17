import Submission.E8KostantConv
import Submission.E8NoKernel
import Submission.E8Character
import Submission.WCFSetup
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_small_height_length

/-!
# The Weyl character formula for the constituents: the `A_ρ`-setup

For an arbitrary dominant weight `Λ` define

  `chV ν μ = K(ν - μ)`,   `euler Λ μ = ∑_{N ∈ W} ε(N) · chV(N · Λ)(μ)`

where `K` is the Kostant partition function (`Submission.E8KostantConv.KP`) and `N · Λ` is the
dot action.  `euler Λ` is the **Euler characteristic of the Verma modules** on the dot-orbit
`W · Λ`, i.e. the Weyl–Kostant multiplicity formula `Σ_N ε(N) dim M(N·Λ)_μ`.

Proved here:

* `WSum_chV` — `A_ρ · chV ν` is the delta function at `ν + ρ`, i.e.
  `∑_{N∈W} ε(N) K(Nρ - η) = [η = ρ]` (the commons identity `E8_weyl_kostant_K`);
* `WSum_euler` — **`A_ρ · euler Λ = A_{Λ+ρ}`**, i.e.
  `∑_{N∈W} ε(N) euler Λ (x - Nρ) = ∑_{N∈W} ε(N) [N(Λ+ρ) = x]`;
* `euler_ht` — the support of `euler Λ` is bounded in height: `euler Λ μ ≠ 0 ⟹ htOf μ ≤ htOf Λ`.

## What remains

Writing `g := euler Λ` for one of the forty dominant weights `Λ` of
`Submission.E8Extract.ord40`, the Weyl character formula `A_ρ · ch L(Λ) = A_{Λ+ρ}` (hence the
Klimyk extraction of the multiplicities of the tensor square) follows from

* (a) `g Λ = 1`
* (b) `g μ ≠ 0 ⟹ Λ - μ ∈ ℕΦ⁺ ∪ {0}`  (`dc`-invariance of `g` + the descent identity
  `WSum_euler` + maximality in the cone order),
* (c) `W`-invariance of `g`,
* (d) the Freudenthal recursion for `g` (the sum of the Freudenthal recursions of the Verma
  characters `chV(N·Λ)`, whose coefficients agree by `Submission.E8Kostant.casOf_dotact`),

via `Submission.E8Character.eq_of_freudenthal` applied to `g` and the table character `Mnu i`
(`Submission.E8ConstChar.MnuQ_*`), which satisfies (a)–(d) by construction.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8WCFC

open Commons.LinearAlgebra.Matrix.Cartan
open Submission.WCFSetup
open Submission.E8Character

/-- The positive roots of `E₈` as a type. -/
abbrev PosR : Type := Submission.E8KostantConv.PosR

/-- The Kostant partition function. -/
noncomputable abbrev KP (δ : Fin 8 → ℤ) : ℕ := Submission.E8KostantConv.KP δ

/-- **The Verma character**: `chV ν μ = K(ν - μ)`. -/
noncomputable def chV (ν : Fin 8 → ℤ) : (Fin 8 → ℤ) → ℚ := fun μ => (KP (ν - μ) : ℚ)

/-- The dot action `M · ν = M(ν + ρ) - ρ`. -/
noncomputable def dot (M : Matrix (Fin 8) (Fin 8) ℤ) (ν : Fin 8 → ℤ) : Fin 8 → ℤ :=
  ap M (ν + rhoV) - rhoV

lemma dot_add_rho (M : Matrix (Fin 8) (Fin 8) ℤ) (ν : Fin 8 → ℤ) :
    dot M ν + rhoV = ap M (ν + rhoV) := by rw [dot]; abel

/-- The alternant of a weight: `A_μ(x) = ∑_M ε(M) [M μ = x]`. -/
noncomputable def alt (μ : Fin 8 → ℤ) : (Fin 8 → ℤ) → ℚ :=
  fun x => ∑ M ∈ WG, (M.det : ℚ) * (if ap M μ = x then 1 else 0)

/-- **The Euler characteristic of the Verma modules on the dot-orbit of `Λ`.** -/
noncomputable def euler (Λ : Fin 8 → ℤ) : (Fin 8 → ℤ) → ℚ :=
  fun μ => ∑ N ∈ WG, (N.det : ℚ) * chV (dot N Λ) μ

/-! ## Heights -/

lemma htOf_rhoV : htOf rhoV = 620 := by
  rw [Submission.E8NoKernel.ht_eq_e8ht, rhoV_eq]
  exact e8ht_rhoZ

lemma htOf_dot (M : Matrix (Fin 8) (Fin 8) ℤ) (ν : Fin 8 → ℤ) :
    htOf (dot M ν) = htOf (ap M (ν + rhoV)) - 620 := by
  rw [dot, htOf_sub, htOf_rhoV]

/-- The two spellings of the simple-root coordinates agree. -/
lemma coords_eq' (γ : Fin 8 → ℤ) :
    Commons.LinearAlgebra.Matrix.Cartan.coords γ = Submission.E8Character.coords γ := by
  funext i
  simp [Commons.LinearAlgebra.Matrix.Cartan.coords, Submission.E8Character.coords, Matrix.mulVec,
    dotProduct, mul_comm]

/-- `posCon` of the cone element `x - w x` for `x` dominant. -/
lemma posCon_dom_sub_wact (L : List (Fin 8)) (x : Fin 8 → ℤ) (hx : ∀ i, 0 ≤ x i) :
    posCon (x - wact L x) := by
  intro i
  rw [← coords_eq']
  exact E8_dom_sub_wact_mem_cone L x hx i

/-! ## The support of the Kostant partition function -/

lemma posCon_of_mem_P {α : Fin 8 → ℤ} (h : α ∈ (E8posRoots.P : Finset (Fin 8 → ℤ))) :
    posCon α := ((E8posRoots.memP α).mp h).2.2

lemma zsmul_eq_nsmul (n : ℕ) {M : Type*} [AddCommGroup M] (a : M) :
    (n : ℤ) • a = n • a := by
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_zsmul, ih, one_zsmul, succ_nsmul]

lemma posCon_sum' {ι : Type*} (s : Finset ι) (g : ι → Fin 8 → ℤ)
    (h : ∀ i ∈ s, posCon (g i)) : posCon (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using posCon_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact posCon_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The support of the Kostant partition function.** -/
lemma KP_posCon {γ : Fin 8 → ℤ} (h : KP γ ≠ 0) : posCon γ := by
  obtain ⟨k, hk⟩ := (Nat.card_ne_zero.mp h).1
  have hk' : γ = ∑ α : PosR, k α • (α : Fin 8 → ℤ) := hk.symm
  rw [hk']
  refine posCon_sum' Finset.univ (fun α => k α • (α : Fin 8 → ℤ)) (fun α _ => ?_)
  rw [← zsmul_eq_nsmul (k α) (α : Fin 8 → ℤ)]
  exact posCon_smul_nonneg (by positivity) (posCon_of_mem_P α.2)

/-! ## Linearity of the Weyl sum -/

lemma WSum_add {f g : (Fin 8 → ℤ) → ℚ} (x : Fin 8 → ℤ) :
    WSum (f + g) x = WSum f x + WSum g x := by
  simp only [WSum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-! ## `A_ρ` of a Verma character is a delta function -/

lemma WSum_chV (ν x : Fin 8 → ℤ) :
    WSum (chV ν) x = if x = ν + rhoV then 1 else 0 := by
  have hcast : WSum (chV ν) x
      = ((∑ M ∈ WG, (M.det : ℤ) * (KP (ap M rhoV - (x - ν)) : ℤ) : ℤ) : ℚ) := by
    rw [WSum]
    simp only [chV]
    push_cast
    refine Finset.sum_congr rfl (fun M _ => ?_)
    rw [show ν - (x - ap M rhoV) = ap M rhoV - (x - ν) from by abel]
  rw [hcast, Submission.E8KostantConv.E8_weyl_kostant_K (x - ν)]
  rw [show (if x - ν = rhoV then (1 : ℤ) else 0)
        = (if x = ν + rhoV then (1 : ℤ) else 0) from
    if_congr (by simp only [sub_eq_iff_eq_add, add_comm]) rfl rfl]
  split <;> norm_num

/-- **`A_ρ · euler Λ = A_{Λ+ρ}`.** -/
theorem WSum_euler (Λ x : Fin 8 → ℤ) :
    WSum (euler Λ) x = alt (Λ + rhoV) x := by
  have hkey : ∀ f : Matrix (Fin 8) (Fin 8) ℤ → Matrix (Fin 8) (Fin 8) ℤ → ℚ,
      (∑ M ∈ WG, (M.det : ℚ) * ∑ N ∈ WG, (N.det : ℚ) * f M N)
        = ∑ N ∈ WG, (N.det : ℚ) * ∑ M ∈ WG, (M.det : ℚ) * f M N := by
    intro f
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun N _ => ?_)
    refine Finset.sum_congr rfl (fun M _ => ?_)
    ring
  have h1 : WSum (euler Λ) x
      = ∑ N ∈ WG, (N.det : ℚ) * WSum (chV (dot N Λ)) x := by
    simp only [euler, WSum]
    rw [hkey]
  rw [h1]
  simp only [WSum_chV]
  rw [alt]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  rw [dot_add_rho]
  by_cases h : x = ap N (Λ + rhoV)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

/-! ## Anti-invariance of the alternant -/

theorem alt_ap (μ x : Fin 8 → ℤ) {M₀ : Matrix (Fin 8) (Fin 8) ℤ} (h₀ : M₀ ∈ WG) :
    alt μ (ap M₀ x) = (M₀.det : ℚ) * alt μ x := by
  classical
  obtain ⟨M₀', hM₀', h₁, h₂⟩ := WG_inv h₀
  have hinj : ∀ a b : Fin 8 → ℤ, ap M₀ a = ap M₀ b → a = b := by
    intro a b hab
    have := congrArg (ap M₀') hab
    rwa [← ap_mul, h₂, ap_one, ← ap_mul, h₂, ap_one] at this
  rw [alt, alt, Finset.mul_sum]
  have hbij : (∑ M ∈ WG, (M.det : ℚ) * (if ap M μ = ap M₀ x then 1 else 0))
      = ∑ N ∈ WG, ((M₀ * N).det : ℚ)
          * (if ap (M₀ * N) μ = ap M₀ x then 1 else 0) := by
    refine (Finset.sum_bij (fun N _ => M₀ * N) ?_ ?_ ?_ ?_).symm
    · intro N hN; exact WG_mul h₀ hN
    · intro N₁ h₁' N₂ h₂' heq
      have := congrArg (fun P : Matrix (Fin 8) (Fin 8) ℤ => M₀' * P) heq
      simpa only [← Matrix.mul_assoc, h₂, Matrix.one_mul] using this
    · intro M hM
      exact ⟨M₀' * M, WG_mul hM₀' hM, by rw [← Matrix.mul_assoc, h₁, Matrix.one_mul]⟩
    · intro N hN; rfl
  rw [hbij]
  refine Finset.sum_congr rfl (fun N hN => ?_)
  rw [Matrix.det_mul, ap_mul]
  by_cases h : ap N μ = x
  · rw [if_pos h, if_pos (by rw [h])]
    push_cast; ring
  · rw [if_neg h, if_neg (fun hh => h (hinj _ _ hh))]
    ring

/-! ## The height bound for the Euler characteristic -/

lemma euler_ht {Λ : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i) (μ : Fin 8 → ℤ) (h : euler Λ μ ≠ 0) :
    htOf μ ≤ htOf Λ := by
  rw [euler] at h
  obtain ⟨N, hN, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hch : chV (dot N Λ) μ ≠ 0 := fun h0 => hterm (by rw [h0, mul_zero])
  have hKP : KP (dot N Λ - μ) ≠ 0 := fun h0 => hch (by simp [chV, h0])
  have hpos := KP_posCon hKP
  have h2 : htOf μ ≤ htOf (dot N Λ) := by
    have := htOf_nonneg hpos
    rw [htOf_sub] at this
    linarith
  obtain ⟨L, rfl⟩ := mem_WG.mp hN
  have h3 : htOf (dot (wactMat L) Λ) = htOf (wact L (Λ + rhoV)) - 620 := by
    rw [htOf_dot, wactMat_ap]
  have h4 : htOf (wact L (Λ + rhoV)) ≤ htOf (Λ + rhoV) := by
    have h5 : posCon (Λ + rhoV - wact L (Λ + rhoV)) :=
      posCon_dom_sub_wact L (Λ + rhoV)
        (fun i => by have := hΛ i; simp only [Pi.add_apply, rhoV, Pi.one_apply]; omega)
    have h6 := htOf_nonneg h5
    rw [htOf_sub] at h6
    linarith
  have h7 : htOf (Λ + rhoV) = htOf Λ + 620 := by rw [htOf_add, htOf_rhoV]
  linarith

/-! ## The value at the top weight -/

lemma posCon_eq_zero_of_htOf_zero {γ : Fin 8 → ℤ} (h : posCon γ) (h0 : htOf γ = 0) :
    γ = 0 := by
  have h1 : ∀ i, E8Character.coords γ i = 0 := by
    intro i
    have h2 : 0 ≤ E8Character.coords γ i := h i
    have h3 : E8Character.coords γ i ≤ htOf γ := by
      rw [htOf_eq]
      exact Finset.single_le_sum (fun j _ => h j) (Finset.mem_univ i)
    omega
  have h4 : E8Character.coords γ = 0 := funext h1
  have h5 := E8Character.mulVec_coords γ
  rw [h4, Matrix.mulVec_zero] at h5
  exact h5.symm

/-- The Kostant partition function at the origin. -/
lemma KP_zero : KP (0 : Fin 8 → ℤ) = 1 := by
  change Submission.E8KostantConv.KP (0 : Fin 8 → ℤ) = 1
  have h := Submission.E8KostantConv.Kbr_eq_KP 0 (0 : Fin 8 → ℤ) (by
    rw [← Submission.E8NoKernel.ht_eq_e8ht, htOf_zero]; norm_num)
  rw [h.symm, Submission.E8KostantConv.Kbr]
  have hbox : Submission.E8KostantConv.box 0
      = {fun _ : PosR => 0} := by
    ext f
    rw [Submission.E8KostantConv.mem_box]
    constructor
    · intro hf
      simp only [Finset.mem_singleton]
      funext α
      exact Nat.le_zero.mp (hf α)
    · intro hf
      rw [Finset.mem_singleton.mp hf]
      intro α
      simp
  rw [hbox, Finset.filter_true_of_mem]
  · simp
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    simp

/-- The dot-orbit terms other than `N = 1` do not contribute at the top weight. -/
lemma KP_dot_sub_self_eq_zero {N : Matrix (Fin 8) (Fin 8) ℤ} (Λ : Fin 8 → ℤ) (hN : N ∈ WG)
    (hΛ : ∀ i, 0 ≤ Λ i) (hne : N ≠ 1) : KP (dot N Λ - Λ) = 0 := by
  by_contra hKP
  have hpc := KP_posCon hKP
  have hnn : 0 ≤ htOf (dot N Λ - Λ) := htOf_nonneg hpc
  obtain ⟨L, rfl⟩ := mem_WG.mp hN
  have h3 : htOf (dot (wactMat L) Λ) = htOf (wact L (Λ + rhoV)) - 620 := by
    rw [htOf_dot, wactMat_ap]
  have h4 : htOf (wact L (Λ + rhoV)) ≤ htOf (Λ + rhoV) := by
    have h5 : posCon (Λ + rhoV - wact L (Λ + rhoV)) :=
      posCon_dom_sub_wact L (Λ + rhoV)
        (fun i => by have := hΛ i; simp only [Pi.add_apply, rhoV, Pi.one_apply]; omega)
    have h6 := htOf_nonneg h5
    rw [htOf_sub] at h6
    linarith
  have h7 : htOf (Λ + rhoV) = htOf Λ + 620 := by rw [htOf_add, htOf_rhoV]
  have h8 : htOf (dot (wactMat L) Λ - Λ) = htOf (dot (wactMat L) Λ) - htOf Λ := htOf_sub _ _
  have h9 : htOf (dot (wactMat L) Λ - Λ) = 0 := by linarith
  have h10 : dot (wactMat L) Λ - Λ = 0 := posCon_eq_zero_of_htOf_zero hpc h9
  apply hne
  have hfix : ap (wactMat L) (Λ + rhoV) = Λ + rhoV := by
    have h11 : dot (wactMat L) Λ = Λ := sub_eq_zero.mp h10
    have := dot_add_rho (wactMat L) Λ
    rw [h11] at this
    exact this.symm
  have hfix' : wact L (Λ + rhoV) = Λ + rhoV := by rwa [wactMat_ap] at hfix
  have hstable := E8_wact_fixes_strict_dominant
    (fun i => by have := hΛ i; simp only [Pi.add_apply, rhoV, Pi.one_apply]; omega) hfix'
  rw [show (1 : Matrix (Fin 8) (Fin 8) ℤ) = wactMat ([] : List (Fin 8)) from wactMat_nil.symm]
  exact wactMat_eq_of_rho_eq (hstable rhoZ)

/-- **`euler Λ` takes the value `1` at the top weight `Λ`** (for `Λ` dominant). -/
lemma euler_top {Λ : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i) : euler Λ Λ = 1 := by
  rw [euler]
  rw [Finset.sum_eq_single (1 : Matrix (Fin 8) (Fin 8) ℤ)]
  · simp only [chV, Matrix.det_one, one_mul]
    rw [show dot 1 Λ - Λ = 0 from by rw [dot, ap_one]; abel]
    rw [KP_zero]
    norm_num
  · intro N hN hNne
    simp only [chV]
    rw [KP_dot_sub_self_eq_zero Λ hN hΛ hNne]
    simp
  · intro h1
    exact absurd WG_one h1

end Submission.E8WCFC
