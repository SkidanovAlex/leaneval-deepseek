import Mathlib
import Submission.Work.KMTAreas.A7Hi.rotationIdentity
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Ortho
import Submission.Work.BourgainPlan.IonescuWainger.ShiftArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_quadratic_weight
import Submission.Work.KMTAreas.A7Hi.variationalNorm_tsum_le
import Submission.Work.KMTAreas.A7Rep.DecimatedVrAux
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral
import Submission.Work.KMTAreas.A7.sublatticeShannonReproduction

namespace Work.KMTAreas.A7Hi

set_option maxHeartbeats 4000000

open MeasureTheory Finset
open scoped BigOperators ENNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Elementary character facts for `q`-torsion frequencies -/

/-- For a `q`-torsion frequency `α` (`q • α = 0`), the character with index `-q z` is trivial. -/
lemma fourier_neg_qmul_eq_one {q : ℕ} {α : Circ} (hα : q • α = 0) (z : ℤ) :
    fourier (T := 1) (-((q : ℤ) * z)) α = 1 := by
  rw [fourier_apply]
  have h2 : (q : ℤ) • α = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hα
  have h3 : ((q : ℤ) * z) • α = 0 := by rw [mul_zsmul, smul_comm, h2, smul_zero]
  rw [show (-((q : ℤ) * z)) • α = 0 from by rw [neg_zsmul, h3, neg_zero],
    AddCircle.toCircle_zero]
  rfl

/-- For a `q`-torsion frequency `α`, the character with index `-m` depends on `m` only modulo `q`. -/
lemma fourier_neg_mod_eq {q : ℕ} {α : Circ} (hα : q • α = 0) (m : ℕ) :
    fourier (T := 1) (-((m : ℕ) : ℤ)) α = fourier (T := 1) (-(((m % q : ℕ) : ℤ))) α := by
  have hdec : ((m : ℕ) : ℤ) = ((m % q : ℕ) : ℤ) + (q : ℤ) * ((m / q : ℕ) : ℤ) := by
    have h : (((m % q : ℕ) : ℤ) + (q : ℤ) * ((m / q : ℕ) : ℤ))
        = ((((m % q : ℕ) + q * (m / q) : ℕ)) : ℤ) := by
      rw [Nat.cast_add, Nat.cast_mul]
    rw [h, Nat.mod_add_div]
  have harg : -((m : ℕ) : ℤ)
      = -(((m % q : ℕ) : ℤ)) + (-((q : ℤ) * ((m / q : ℕ) : ℤ))) := by
    rw [hdec]; ring
  rw [harg, fourier_add, fourier_neg_qmul_eq_one hα, mul_one]

/-- The phase of a rotated window at a decimated point: the product of the `n₀`-character and the
`x`-character collapses to the `q`-periodic character of `r + n₀`. -/
lemma fourier_phase_collapse {q : ℕ} {α : Circ} (hα : q • α = 0) (n₀ : ℕ) (z : ℤ) (r : ℕ) :
    fourier (T := 1) (-(n₀ : ℤ)) α * fourier (T := 1) (-(((q : ℤ) * z + r : ℤ))) α
      = fourier (T := 1) (-((((r + n₀) % q : ℕ) : ℤ))) α := by
  rw [← fourier_add]
  have harg : -(n₀ : ℤ) + -(((q : ℤ) * z + r : ℤ))
      = -((q : ℤ) * z) + (-(((r + n₀ : ℕ) : ℤ))) := by
    push_cast; ring
  rw [harg, fourier_add, fourier_neg_qmul_eq_one hα, one_mul, fourier_neg_mod_eq hα]

/-- The `x`-character of the synthesis at a decimated point. -/
lemma fourier_neg_decim_eq {q : ℕ} {α : Circ} (hα : q • α = 0) (r : ℕ) (z : ℤ) :
    fourier (T := 1) (-(((q : ℤ) * z + r : ℤ))) α = fourier (T := 1) (-(r : ℤ)) α := by
  have harg : -(((q : ℤ) * z + r : ℤ)) = -((q : ℤ) * z) + (-(r : ℤ)) := by ring
  rw [harg, fourier_add, fourier_neg_qmul_eq_one hα, one_mul]

/-- **Reindexing a sum over `range q` by the cyclic shift `n₀ ↦ (r + n₀) % q`.** -/
lemma sum_range_add_mod (q : ℕ) (hq : 0 < q) (r : ℕ) (F : ℕ → ENNReal) :
    (∑ n₀ ∈ Finset.range q, F ((r + n₀) % q)) = ∑ s ∈ Finset.range q, F s := by
  have hinj : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q, (r + a) % q = (r + b) % q → a = b := by
    intro a ha b hb hab
    have ha' : a < q := Finset.mem_range.mp ha
    have hb' : b < q := Finset.mem_range.mp hb
    rcases le_total a b with hle | hle
    · have h1 : (r + a) ≡ (r + b) [MOD q] := hab
      have h2 : q ∣ (r + b) - (r + a) := (Nat.modEq_iff_dvd' (by omega)).mp h1
      have h3 : (r + b) - (r + a) = b - a := by omega
      rw [h3] at h2
      have h4 : b - a = 0 := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
      omega
    · have h1 : (r + b) ≡ (r + a) [MOD q] := hab.symm
      have h2 : q ∣ (r + a) - (r + b) := (Nat.modEq_iff_dvd' (by omega)).mp h1
      have h3 : (r + a) - (r + b) = a - b := by omega
      rw [h3] at h2
      have h4 : a - b = 0 := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
      omega
  have himg : (Finset.range q).image (fun n₀ => (r + n₀) % q) = Finset.range q := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ hq)
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← Finset.sum_image hinj, himg]

/-- Interchanging a `tsum` over `ℤ` with a finite sum in `ℝ≥0∞`. -/
lemma tsum_finset_sum_ennreal {ι : Type*} (s : Finset ι) (g : ℤ → ι → ENNReal) :
    (∑' x : ℤ, ∑ i ∈ s, g x i) = ∑ i ∈ s, ∑' x : ℤ, g x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : ∀ x : ℤ, (∑ i ∈ insert a s, g x i) = g x a + ∑ i ∈ s, g x i :=
        fun x => Finset.sum_insert ha
      rw [tsum_congr h1, ENNReal.tsum_add, ih, Finset.sum_insert ha]


/-! ## The character collapse at decimated points -/

/-- `winRot` at a decimated point `q * z + r` is the rephased synthesis with the phase `r + n₀`
reduced modulo `q`. -/
lemma winRot_decim (A : Finset Circ) (f : ℕ → Circ → ℤ → ℂ) {q : ℕ}
    (hA : ∀ α ∈ A, q • α = 0) (n₀ r n : ℕ) (z : ℤ) :
    winRot A (f n) (n₀ : ℤ) ((q : ℤ) * z + (r : ℤ))
      = ∑ α ∈ A, fourier (T := 1) (-(((r + n₀) % q : ℕ) : ℤ)) α
          * f n α ((q : ℤ) * z + (r : ℤ)) := by
  unfold winRot
  refine Finset.sum_congr rfl fun α hα => ?_
  have hc := fourier_phase_collapse (hA α hα) n₀ z r
  calc fourier (T := 1) (-(n₀ : ℤ)) α
        * (fourier (T := 1) (-(((q : ℤ) * z + (r : ℤ)))) α
            * f n α ((q : ℤ) * z + (r : ℤ)))
      = (fourier (T := 1) (-(n₀ : ℤ)) α
          * fourier (T := 1) (-(((q : ℤ) * z + (r : ℤ)))) α)
          * f n α ((q : ℤ) * z + (r : ℤ)) := by ring
    _ = fourier (T := 1) (-(((r + n₀) % q : ℕ) : ℤ)) α
          * f n α ((q : ℤ) * z + (r : ℤ)) := by rw [hc]

/-- `winSynth` at a decimated point `q * z + r` is the rephased synthesis with the phase `r`. -/
lemma winSynth_decim (A : Finset Circ) (f : ℕ → Circ → ℤ → ℂ) {q : ℕ}
    (hA : ∀ α ∈ A, q • α = 0) (r n : ℕ) (z : ℤ) :
    winSynth A (f n) ((q : ℤ) * z + (r : ℤ))
      = ∑ α ∈ A, fourier (T := 1) (-(r : ℤ)) α * f n α ((q : ℤ) * z + (r : ℤ)) := by
  unfold winSynth
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [fourier_neg_decim_eq (hA α hα) r z]

/-- For a family `g` of `ℓ²` sequences all band-limited to the *same* set `E`, and constants `c`,
the finite rephased sum `∑_{α ∈ A} c α · g α` is `ℓ²` and band-limited to `E`. -/
lemma rephrase_support (A : Finset Circ) (g : Circ → ℤ → ℂ) (c : Circ → ℂ) (E : Set Circ)
    (hg : ∀ α ∈ A, ∃ hh : Memℓp (g α) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (g α) hh E) :
    ∃ hh : Memℓp (fun x : ℤ => ∑ α ∈ A, c α * g α x) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (fun x : ℤ => ∑ α ∈ A, c α * g α x) hh E := by
  classical
  have hmem : ∀ i : ↥A, Memℓp (fun x : ℤ => c i.1 * g i.1 x) 2 :=
    fun i => ((hg i.1 i.2).choose).const_mul (c i.1)
  have hsup : ∀ i : ↥A, Work.BourgainPlan.IonescuWainger.HasFreqSupport
      (fun x : ℤ => c i.1 * g i.1 x) (hmem i) E :=
    fun i => Work.BourgainPlan.IonescuWainger.hasFreqSupport_const_mul
      ((hg i.1 i.2).choose) ((hg i.1 i.2).choose_spec) (c i.1)
  have hsum : Work.BourgainPlan.IonescuWainger.HasFreqSupport
      (fun x : ℤ => ∑ i : ↥A, c i.1 * g i.1 x)
      (Work.BourgainPlan.IonescuWainger.memℓp_sum hmem) (⋃ _i : ↥A, E) :=
    Work.BourgainPlan.IonescuWainger.hasFreqSupport_sum (f := fun i : ↥A => fun x : ℤ => c i.1 * g i.1 x)
      (hf := hmem) (hE := hsup)
  have hcoe : (fun x : ℤ => ∑ i : ↥A, c i.1 * g i.1 x) = fun x : ℤ => ∑ α ∈ A, c α * g α x := by
    funext x
    exact Finset.sum_coe_sort A (fun α => c α * g α x)
  have hmemA : Memℓp (fun x : ℤ => ∑ α ∈ A, c α * g α x) 2 := hcoe ▸ Work.BourgainPlan.IonescuWainger.memℓp_sum hmem
  have h2 := Work.BourgainPlan.IonescuWainger.hasFreqSupport_mono
    (E := ⋃ _i : ↥A, E) (E' := E) (Set.iUnion_subset fun _ => subset_rfl) hsum
  exact ⟨hmemA, Work.BourgainPlan.IonescuWainger.hasFreqSupport_congr
    (hfun := hcoe) (hh := Work.BourgainPlan.IonescuWainger.memℓp_sum hmem) (hh' := hmemA) h2⟩

/-- Instantiation of `rephrase_support` to the rephased synthesis of the target. -/
lemma rephrase_memℓp_support (A : Finset Circ) (f : ℕ → Circ → ℤ → ℂ) (δ : ℝ)
    (hbd : ∀ (n : ℕ) (α : Circ), α ∈ A → ∃ hh : Memℓp (f n α) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport (f n α) hh
        (Work.BourgainPlan.IonescuWainger.arcSet 0 δ)) (s n : ℕ) :
    ∃ hh : Memℓp (fun x : ℤ => ∑ α ∈ A, fourier (T := 1) (-(s : ℤ)) α * f n α x) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (fun x : ℤ => ∑ α ∈ A, fourier (T := 1) (-(s : ℤ)) α * f n α x) hh
        (Work.BourgainPlan.IonescuWainger.arcSet 0 δ) :=
  rephrase_support A (f n) (fun α => fourier (T := 1) (-(s : ℤ)) α)
    (Work.BourgainPlan.IonescuWainger.arcSet 0 δ) (fun α hα => hbd n α hα)

/-! ## Local (self-contained) versions of the two supporting estimates -/

/-- Splitting a `tsum` over `ℤ` into its residue classes modulo `q` (for `ℝ≥0∞`-valued families). -/
lemma periodDecompLocal (q : ℕ) (hq : 0 < q) (F : ℤ → ENNReal) :
    (∑' x : ℤ, F x) = ∑ r ∈ Finset.range q, ∑' z : ℤ, F ((q : ℤ) * z + (r : ℤ)) := by
  haveI : NeZero q := ⟨by omega⟩
  let E : Fin q × ℤ ≃ ℤ := (Equiv.prodComm (Fin q) ℤ).trans (Int.divModEquiv q).symm
  have hE : ∀ (y : Fin q) (k : ℤ), E (y, k) = (y : ℤ) + (k : ℤ) * (q : ℤ) := by
    intro y k
    simp only [E, Equiv.trans_apply, Equiv.prodComm_apply, Int.divModEquiv_symm_apply,
      Prod.swap_prod_mk]
    ring
  rw [(Equiv.tsum_eq E F).symm]
  rw [show (∑' c : Fin q × ℤ, F (E c))
      = ∑' c : Fin q × ℤ, (fun y k => F (E (y, k))) c.1 c.2 from rfl]
  rw [ENNReal.tsum_prod (f := fun (y : Fin q) (k : ℤ) => F (E (y, k)))]
  simp only [hE]
  have htf : (∑' y : Fin q, ∑' (z : ℤ), F ((y : ℤ) + (z : ℤ) * (q : ℤ)))
      = ∑ y : Fin q, ∑' (z : ℤ), F ((y : ℤ) + (z : ℤ) * (q : ℤ)) :=
    tsum_fintype (fun y : Fin q => ∑' (z : ℤ), F ((y : ℤ) + (z : ℤ) * (q : ℤ)))
  have hfr : (∑ y : Fin q, ∑' (z : ℤ), F ((y : ℤ) + (z : ℤ) * (q : ℤ)))
      = ∑ r ∈ Finset.range q, ∑' (z : ℤ), F ((r : ℤ) + (z : ℤ) * (q : ℤ)) :=
    Fin.sum_univ_eq_sum_range (fun r : ℕ => ∑' (z : ℤ), F ((r : ℤ) + (z : ℤ) * (q : ℤ))) q
  rw [htf, hfr]
  refine Finset.sum_congr rfl fun r _ => tsum_congr fun z => ?_
  rw [add_comm, mul_comm]

/-- **The decimated lattice comparison.**  If a summable kernel `K` reproduces every band-`β`
`ℓ²` sequence from its samples on the coset `q ℤ + r₀`, and its mass on each coset of `q ℤ` is at
most `C₀`, then the `ℓᵖ(ℤ; Vʳ)` norms of the samples on the cosets `q ℤ + r₁` and `q ℤ + r₀` are
comparable with constant `C₀ ^ p`. -/
lemma decimLatticeCompareLocal (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 1 ≤ r)
    (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : 0 < β) (C₀ : ℝ) (hC₀ : 0 < C₀) (hC₀1 : 1 ≤ C₀)
    (K : ℤ → ℂ) (hKsum : Summable (fun m : ℤ => ‖K m‖))
    (hKspread : ∀ s : ℤ, (∑' l : ℤ, ‖K (q * l + s)‖) ≤ C₀)
    (r₀ r₁ : ℤ)
    (hid : ∀ (G : ℤ → ℂ) (hG : Memℓp G 2)
        (hsupp : Work.BourgainPlan.IonescuWainger.HasFreqSupport G hG
          (Work.BourgainPlan.IonescuWainger.arcSet 0 β)) (x : ℤ),
        G x = ∑' m : ℤ, G (q * m + r₀) * K (x - (q * m + r₀)))
    (H : ℕ → ℤ → ℂ) (hH : ∀ n, Memℓp (H n) 2)
    (hsuppH : ∀ n, Work.BourgainPlan.IonescuWainger.HasFreqSupport (H n) (hH n)
      (Work.BourgainPlan.IonescuWainger.arcSet 0 β)) :
    (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => H n (q * z + r₁))) ^ p)
      ≤ ENNReal.ofReal (C₀ ^ p) *
        (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => H n (q * z + r₀))) ^ p) := by
  set κ : ℤ → ℂ := fun l => K (q * l + (r₁ - r₀)) with hκ
  have hκsum : Summable (fun l : ℤ => ‖κ l‖) := by
    refine hKsum.comp_injective ?_
    intro a b hab
    simp only at hab
    have h1 : (q : ℤ) * a = (q : ℤ) * b := add_right_cancel hab
    exact mul_left_cancel₀ (by exact_mod_cast hq.ne' : ((q : ℤ)) ≠ 0) h1
  have henorm : ∀ z : ℂ, ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
    intro z
    rw [enorm_eq_nnnorm]
    exact ENNReal.coe_nnreal_eq (nnnorm z)
  have hcoset : ∀ s : ℤ, (∑' l : ℤ, ‖κ l‖ₑ) ≤ ENNReal.ofReal C₀ := by
    intro s
    have h1 : (∑' l : ℤ, ‖κ l‖ₑ) = ENNReal.ofReal (∑' l : ℤ, ‖κ l‖) := by
      rw [show (fun l : ℤ => ‖κ l‖ₑ) = fun l : ℤ => ENNReal.ofReal ‖κ l‖ from
        funext fun l => henorm (κ l),
        ENNReal.ofReal_tsum_of_nonneg (fun l => norm_nonneg _) hκsum]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hKspread (r₁ - r₀))
  have hpoint : ∀ (n : ℕ) (z : ℤ),
      H n (q * z + r₁) = ∑' m : ℤ, κ (z - m) * H n (q * m + r₀) := by
    intro n z
    rw [hid (H n) (hH n) (hsuppH n) (q * z + r₁)]
    refine tsum_congr fun m => ?_
    have harg : q * z + r₁ - (q * m + r₀) = q * (z - m) + (r₁ - r₀) := by ring
    rw [harg]
    simp only [hκ]
    ring
  have hV : ∀ z : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => H n (q * z + r₁))
      ≤ ∑' m : ℤ, ‖κ (z - m)‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => H n (q * m + r₀)) := by
    intro z
    have hfun : (fun n : ℕ => H n (q * z + r₁))
        = fun n : ℕ => ∑' m : ℤ, κ (z - m) * H n (q * m + r₀) :=
      funext fun n => hpoint n z
    rw [hfun]
    exact Work.KMTAreas.A7Hi.variationalNorm_tsum_le r hr (fun m : ℤ => κ (z - m))
      (fun m n => H n (q * m + r₀))
  have hrow : ∀ z : ℤ, (∑' m : ℤ, ‖κ (z - m)‖ₑ) ≤ ENNReal.ofReal C₀ := by
    intro z
    have h1 : (∑' m : ℤ, ‖κ (z - m)‖ₑ) = ∑' l : ℤ, ‖κ l‖ₑ :=
      Equiv.tsum_eq (Equiv.subLeft z) (fun l : ℤ => ‖κ l‖ₑ)
    rw [h1]
    exact hcoset (r₁ - r₀)
  have hcol : ∀ m : ℤ, (∑' z : ℤ, ‖κ (z - m)‖ₑ) ≤ ENNReal.ofReal C₀ := by
    intro m
    have h1 : (∑' z : ℤ, ‖κ (z - m)‖ₑ) = ∑' l : ℤ, ‖κ l‖ₑ := by
      exact Equiv.tsum_eq (Equiv.addRight (-m)) (fun l : ℤ => ‖κ l‖ₑ)
    rw [h1]
    exact hcoset (r₁ - r₀)
  have hschur := Work.KMTAreas.A7Rep.weightedHolderTsum (p := p) (hp := hp)
    (W := fun z m => ‖κ (z - m)‖ₑ)
    (v := fun m => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => H n (q * m + r₀)))
    (A := C₀) (B := C₀) hC₀.le hC₀.le hrow hcol
  calc (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => H n (q * z + r₁))) ^ p)
      ≤ ∑' z : ℤ, (∑' m : ℤ, ‖κ (z - m)‖ₑ *
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => H n (q * m + r₀))) ^ p :=
        ENNReal.tsum_le_tsum fun z =>
          ENNReal.rpow_le_rpow (hV z) (le_of_lt (lt_trans zero_lt_one hp))
    _ ≤ ENNReal.ofReal (C₀ ^ (p - 1) * C₀) *
          (∑' m : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => H n (q * m + r₀))) ^ p) := hschur
    _ = ENNReal.ofReal (C₀ ^ p) *
          (∑' m : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => H n (q * m + r₀))) ^ p) := by
        congr 1
        rw [show C₀ ^ p = C₀ ^ ((p - 1) + 1) by rw [sub_add_cancel], Real.rpow_add hC₀,
          Real.rpow_one]

end

end Work.KMTAreas.A7Hi
