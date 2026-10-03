import Mathlib
import Submission.Work.Peluse.Prop36SW.flatDefs

/-!
# The **flat** (`Fin n → ℤ`) peel of the §5 chain

`lstatePeelAbs` (`lstatePeelAbs.lean`) is the analytic peel of the chain in the *nested* parameter
type `PeelParam`, and `flatDefs.lean` encodes a nested parameter into the flat type
`Fin (n + 2t') → ℤ` along `toFin`, with the parameter set `shiftSetFin` and the flat family
`peelGFin`.

This file proves `lstatePeelFin`: the *transport* of the nested peel's output state to the flat
parameter set.  It is a pure `Finset`/transport argument — `lstatePeelAbs` is reused verbatim.

The transport rests on a bijection

    PeelParam p M₁ M₂ A γ' t' s₀  ≃  ↥(paramBox M₂) × ↥(shiftSetFin p M₁ M₂ A γ' t' s₀)

which forgets the (redundant) box coordinate of `PeelParam`; every fibre of `toFin` has cardinality
`(paramBox M₂).card`, so the two normalised averages agree.

The one subtlety is that `toFin`'s parity test `(k : ℕ) % 2 = 0` is on the *absolute* coordinate
`k`, not on `k - n`; hence for **odd** `n` the shift pair `(false, true)` of `shiftC` is read off the
coordinates `(n + 2i, n + 2i + 1)` in the *swapped* order.  Since the shift pairs of `PeelParam`
range over the symmetric product `arithIcc c L × arithIcc c L`, the swap is a bijection of the index
set, and the averaged sums are unchanged (`peelSigma` below is `id` for even `n` and the swap for odd
`n`; `peelGFin (toFin q) = peelG (peelSigma q)`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-! ## 1. The coordinates of `toFin` -/

/-- The first `n` coordinates of `toFin q` are the old parameter `q.1.1.1`. -/
theorem restr_toFin {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) :
    restr n t' (toFin p M₁ M₂ A γ' t' s₀ q) = q.1.1.1 := by
  funext i
  simp [restr, toFin]

/-- The `i`-th `shiftC` coordinate `(false)` of `toFin q`.  Because the parity test of `toFin` is on
the absolute coordinate, this is the **first** component of the `i`-th shift pair exactly when `n`
is even (`n % 2 = 0`) and the **second** one when `n` is odd. -/
theorem shiftC_toFin_false {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) (q : PeelParam p M₁ M₂ A γ' t' s₀) (i : Fin t') :
    shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) i false
      = (if n % 2 = 0 then ((q.2 i).1 : ℤ) else ((q.2 i).2 : ℤ)) := by
  simp only [shiftC, Bool.false_eq_true, ↓reduceIte, toFin]
  have hk : ¬ (n + 2 * (i : ℕ) + 0 < n) := by omega
  have hmod : (n + 2 * (i : ℕ) + 0) % 2 = n % 2 := by
    rw [add_zero]; exact Nat.add_mul_mod_self_left n 2 i
  have hdiv : (n + 2 * (i : ℕ) + 0 - n) / 2 = (i : ℕ) := by
    rw [add_zero, Nat.add_sub_cancel_left, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  rw [dif_neg hk, hmod]
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_pos h]
    exact congrArg (fun j : Fin t' => ((q.2 j).1 : ℤ)) (Fin.ext hdiv)
  · rw [if_neg h, if_neg h]
    exact congrArg (fun j : Fin t' => ((q.2 j).2 : ℤ)) (Fin.ext hdiv)

/-- The `i`-th `shiftC` coordinate `(true)` of `toFin q` (see `shiftC_toFin_false`). -/
theorem shiftC_toFin_true {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) (q : PeelParam p M₁ M₂ A γ' t' s₀) (i : Fin t') :
    shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) i true
      = (if n % 2 = 0 then ((q.2 i).2 : ℤ) else ((q.2 i).1 : ℤ)) := by
  simp only [shiftC, reduceIte, toFin]
  have hk : ¬ (n + 2 * (i : ℕ) + 1 < n) := by omega
  have hmod : (n + 2 * (i : ℕ) + 1) % 2 = (n % 2 + 1) % 2 := by
    have h0 : n + 2 * (i : ℕ) + 1 = (n + 2 * (i : ℕ)) + 1 := by omega
    rw [h0, Nat.add_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by norm_num : 1 < 2)]
  have hdiv : (n + 2 * (i : ℕ) + 1 - n) / 2 = (i : ℕ) := by
    have h2 : n + 2 * (i : ℕ) + 1 - n = 2 * (i : ℕ) + 1 := by omega
    rw [h2, Nat.mul_add_div (by norm_num : 0 < 2), Nat.div_eq_of_lt (by norm_num : 1 < 2),
      add_zero]
  rw [dif_neg hk, hmod]
  by_cases h : n % 2 = 0
  · have hz : (n % 2 + 1) % 2 = 1 := by
      rw [h, zero_add, Nat.mod_eq_of_lt (by norm_num : (1 : ℕ) < 2)]
    rw [hz, if_neg (by norm_num : ¬ (1 : ℕ) = 0), if_pos h]
    exact congrArg (fun j : Fin t' => ((q.2 j).2 : ℤ)) (Fin.ext hdiv)
  · have hn : n % 2 = 1 := by omega
    have hz : (n % 2 + 1) % 2 = 0 := by rw [hn]
    rw [hz, if_pos rfl, if_neg h]
    exact congrArg (fun j : Fin t' => ((q.2 j).1 : ℤ)) (Fin.ext hdiv)

/-- `toFin` is injective as soon as the box coordinates agree. -/
theorem toFin_inj_of_box {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) (q q' : PeelParam p M₁ M₂ A γ' t' s₀)
    (hb : q.1.2.1 = q'.1.2.1)
    (hf : toFin p M₁ M₂ A γ' t' s₀ q = toFin p M₁ M₂ A γ' t' s₀ q') : q = q' := by
  have hrestr : restr n t' (toFin p M₁ M₂ A γ' t' s₀ q)
      = restr n t' (toFin p M₁ M₂ A γ' t' s₀ q') := by rw [hf]
  have hfun : q.1.1.1 = q'.1.1.1 := by
    funext i
    have h1 := congrFun hrestr i
    rwa [restr_toFin, restr_toFin] at h1
  have hab : q.1 = q'.1 := Prod.ext (Subtype.ext hfun) (Subtype.ext hb)
  cases q with | mk ab sh =>
  cases q' with | mk ab' sh' =>
  simp only at hab hf ⊢
  subst ab'
  congr 1
  funext i
  have h1 : shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ ⟨ab, sh⟩) i false
      = shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ ⟨ab, sh'⟩) i false := by rw [hf]
  have h2 : shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ ⟨ab, sh⟩) i true
      = shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ ⟨ab, sh'⟩) i true := by rw [hf]
  rw [shiftC_toFin_false, shiftC_toFin_false] at h1
  rw [shiftC_toFin_true, shiftC_toFin_true] at h2
  by_cases h : n % 2 = 0
  · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa only [h, if_true] using h1
    · simpa only [h, if_true] using h2
  · refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa only [h, if_false] using h2
    · simpa only [h, if_false] using h1

/-! ## 2. The parity swap and `sigma` -/

/-- The swap of every shift pair of a nested parameter. -/
def peelSwap {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) : PeelParam p M₁ M₂ A γ' t' s₀ :=
  ⟨q.1, fun i => ((q.2 i).2, (q.2 i).1)⟩

theorem peelSwap_invol {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    Function.Involutive (peelSwap p M₁ M₂ A γ' t' s₀) := by
  intro q
  simp only [peelSwap]

/-- The swap as an equivalence of the nested parameter type. -/
def peelSwapEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    PeelParam p M₁ M₂ A γ' t' s₀ ≃ PeelParam p M₁ M₂ A γ' t' s₀ :=
  Equiv.ofBijective _ ((peelSwap_invol p M₁ M₂ A γ' t' s₀).bijective)

theorem peelSwapEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ)
    (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) (q : PeelParam p M₁ M₂ A γ' t' s₀) :
    peelSwapEquiv p M₁ M₂ A γ' t' s₀ q = peelSwap p M₁ M₂ A γ' t' s₀ q := rfl

/-- `id` for even `n`, the swap for odd `n`: the involution `σ` with
`peelGFin (toFin q) = peelG (σ q)`. -/
def peelSigma {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) : PeelParam p M₁ M₂ A γ' t' s₀ :=
  if n % 2 = 0 then q else peelSwap p M₁ M₂ A γ' t' s₀ q

/-- The flat coefficient read at `toFin q` is the nested coefficient at `peelSigma q`. -/
theorem peelPFin_toFin {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) (s : PeelSlot s₀) :
    peelPFin p t' s₀ s (toFin p M₁ M₂ A γ' t' s₀ q)
      = peelP p M₁ M₂ A γ' t' s₀ s (peelSigma p M₁ M₂ A γ' t' s₀ q) := by
  simp only [peelPFin, peelP]
  rw [restr_toFin]
  congr 1
  by_cases h : n % 2 = 0 <;> simp [peelSigma, peelSwap, h]

/-- The flat family read at `toFin q` **is** the nested family at `peelSigma q`. -/
theorem peelGFin_toFin {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (g : (Fin n → ℤ) → ℤ → ℂ) (q : PeelParam p M₁ M₂ A γ' t' s₀) :
    peelGFin t' g (toFin p M₁ M₂ A γ' t' s₀ q)
      = peelG p M₁ M₂ A γ' t' s₀ g (peelSigma p M₁ M₂ A γ' t' s₀ q) := by
  by_cases hn : n % 2 = 0
  · have hsig : peelSigma p M₁ M₂ A γ' t' s₀ q = q := by simp only [peelSigma, hn, if_true]
    rw [hsig]
    have hF : g (restr n t' (toFin p M₁ M₂ A γ' t' s₀ q)) = g (q.1.1.1) := by
      rw [restr_toFin]
    have hsh : (fun i => ((shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) i false,
          shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) i true)))
        = (fun i => ((((q).2 i).1 : ℤ), (((q).2 i).2 : ℤ))) := by
      funext i
      rw [shiftC_toFin_false, shiftC_toFin_true]
      simp only [hn, if_true]
    simp only [peelGFin, peelG]
    rw [hsh, hF]
  · have hsig : peelSigma p M₁ M₂ A γ' t' s₀ q = peelSwap p M₁ M₂ A γ' t' s₀ q := by
      simp only [peelSigma, hn, if_false]
    rw [hsig]
    have hF : g (restr n t' (toFin p M₁ M₂ A γ' t' s₀ q))
        = g ((peelSwap p M₁ M₂ A γ' t' s₀ q).1.1.1) := by
      rw [restr_toFin]
      simp only [peelSwap]
    have hsh : (fun i => ((shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) i false,
          shiftC n t' (toFin p M₁ M₂ A γ' t' s₀ q) i true)))
        = (fun i => ((((peelSwap p M₁ M₂ A γ' t' s₀ q).2 i).1 : ℤ),
            (((peelSwap p M₁ M₂ A γ' t' s₀ q).2 i).2 : ℤ))) := by
      funext i
      rw [shiftC_toFin_false, shiftC_toFin_true]
      simp only [hn, if_false]
      simp only [peelSwap]
    simp only [peelGFin, peelG]
    rw [hsh, hF]

/-! ## 3. The bijection `PeelParam ≃ paramBox × shiftSetFin` -/

/-- The (redundant) box coordinate of a nested parameter. -/
def peelBox {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) : ↥(paramBox (k := fun _ : ι => 1) M₂) :=
  ⟨q.1.2.1, q.1.2.2⟩

/-- The flat parameter of a nested one. -/
def peelImg {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀) :=
  ⟨toFin p M₁ M₂ A γ' t' s₀ q, Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩⟩

/-- The encoding of the nested parameter set into the box times the flat parameter set. -/
def peelPhi {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    PeelParam p M₁ M₂ A γ' t' s₀ →
      ↥(paramBox (k := fun _ : ι => 1) M₂) × ↥(shiftSetFin p M₁ M₂ A γ' t' s₀) :=
  fun q => (peelBox p M₁ M₂ A γ' t' s₀ q, peelImg p M₁ M₂ A γ' t' s₀ q)

theorem peelPhi_injective {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    Function.Injective (peelPhi p M₁ M₂ A γ' t' s₀) := by
  intro q q' h
  have hb : q.1.2.1 = q'.1.2.1 :=
    congrArg (fun y => (y.1 : Slot ι (fun _ => 1) → ℤ)) (congrArg Prod.fst h)
  have hf : toFin p M₁ M₂ A γ' t' s₀ q = toFin p M₁ M₂ A γ' t' s₀ q' :=
    congrArg Subtype.val (congrArg Prod.snd h)
  exact toFin_inj_of_box p M₁ M₂ A γ' t' s₀ q q' hb hf

theorem peelPhi_surjective {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    Function.Surjective (peelPhi p M₁ M₂ A γ' t' s₀) := by
  rintro ⟨b, x⟩
  obtain ⟨q₀, -, hq₀⟩ := Finset.mem_image.mp x.2
  refine ⟨⟨⟨q₀.1.1, ⟨b.1, b.2⟩⟩, q₀.2⟩, ?_⟩
  refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
  rw [← hq₀]
  rfl

/-- **The parameter set of one peel is the product of the box and the flat parameter set.** -/
def peelEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    PeelParam p M₁ M₂ A γ' t' s₀ ≃
      ↥(paramBox (k := fun _ : ι => 1) M₂) × ↥(shiftSetFin p M₁ M₂ A γ' t' s₀) :=
  Equiv.ofBijective _
    ⟨peelPhi_injective p M₁ M₂ A γ' t' s₀, peelPhi_surjective p M₁ M₂ A γ' t' s₀⟩

theorem peelEquiv_apply {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (q : PeelParam p M₁ M₂ A γ' t' s₀) :
    (peelEquiv p M₁ M₂ A γ' t' s₀ q).2.1 = toFin p M₁ M₂ A γ' t' s₀ q := rfl

/-- The cardinality of the nested parameter set. -/
theorem card_peelParam {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1)) :
    Fintype.card (PeelParam p M₁ M₂ A γ' t' s₀)
      = (paramBox (k := fun _ : ι => 1) M₂).card * (shiftSetFin p M₁ M₂ A γ' t' s₀).card := by
  rw [Fintype.card_congr (peelEquiv p M₁ M₂ A γ' t' s₀), Fintype.card_prod,
    Fintype.card_coe, Fintype.card_coe]

/-- **The fibre-average identity**: summing over the nested parameter set is `(paramBox M₂).card`
copies of the sum over the flat parameter set. -/
theorem sum_toFin {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (Ψ : (Fin (n + 2 * t') → ℤ) → ℝ) :
    ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, Ψ (toFin p M₁ M₂ A γ' t' s₀ q)
      = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) *
        ∑ x : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀), Ψ x.1 := by
  have h1 : ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, Ψ (toFin p M₁ M₂ A γ' t' s₀ q)
      = ∑ y : ↥(paramBox (k := fun _ : ι => 1) M₂) × ↥(shiftSetFin p M₁ M₂ A γ' t' s₀),
          (fun z => Ψ z.2.1) y := by
    rw [← Equiv.sum_comp (peelEquiv p M₁ M₂ A γ' t' s₀) (fun z :
      ↥(paramBox (k := fun _ : ι => 1) M₂) × ↥(shiftSetFin p M₁ M₂ A γ' t' s₀) => Ψ z.2.1)]
    exact Finset.sum_congr rfl (fun q _ => by rw [peelEquiv_apply])
  rw [h1, Fintype.sum_prod_type]
  rw [show (∑ x : ↥(paramBox (k := fun _ : ι => 1) M₂),
        ∑ y : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀), Ψ ↑(x, y).2)
      = ∑ x : ↥(paramBox (k := fun _ : ι => 1) M₂),
        ∑ y : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀), Ψ y.1 from
    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => rfl))]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-! ## 4. The pointwise identity of the summands -/

/-- The flat summand at `toFin q` **is** the nested summand at `peelSigma q`. -/
theorem boxNorm_toFin_eq {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (A : Finset (Fin n → ℤ)) (γ' : ℝ) (t' : ℕ)
    (s₀ : Slot ι (fun _ => 1)) (g : (Fin n → ℤ) → ℤ → ℂ) (N : ℕ)
    (kω : SlotSet ι (fun _ => 1) → ℕ) (q : PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Slot (PeelSlot s₀) (fun _ => 1) → ℤ) :
    boxNorm (Fintype.card (FamIdx (peelKω kω s₀)))
      (fun j : Fin (Fintype.card (FamIdx (peelKω kω s₀))) =>
        pDirFamG (peelPFin p t' s₀) M₁ (toFin p M₁ M₂ A γ' t' s₀ q) a'
          ((Fintype.equivFin (FamIdx (peelKω kω s₀))).symm j))
      (symIcc N) (peelGFin t' g (toFin p M₁ M₂ A γ' t' s₀ q))
    = boxNorm (Fintype.card (FamIdx (peelKω kω s₀)))
      (fun j : Fin (Fintype.card (FamIdx (peelKω kω s₀))) =>
        pDirFamG (peelP p M₁ M₂ A γ' t' s₀) M₁ (peelSigma p M₁ M₂ A γ' t' s₀ q) a'
          ((Fintype.equivFin (FamIdx (peelKω kω s₀))).symm j))
      (symIcc N) (peelG p M₁ M₂ A γ' t' s₀ g (peelSigma p M₁ M₂ A γ' t' s₀ q)) := by
  have hP : (fun j : Fin (Fintype.card (FamIdx (peelKω kω s₀))) =>
        pDirFamG (peelPFin p t' s₀) M₁ (toFin p M₁ M₂ A γ' t' s₀ q) a'
          ((Fintype.equivFin (FamIdx (peelKω kω s₀))).symm j))
      = (fun j : Fin (Fintype.card (FamIdx (peelKω kω s₀))) =>
        pDirFamG (peelP p M₁ M₂ A γ' t' s₀) M₁ (peelSigma p M₁ M₂ A γ' t' s₀ q) a'
          ((Fintype.equivFin (FamIdx (peelKω kω s₀))).symm j)) := by
    funext j
    simp only [pDirFamG, pDirG]
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by rw [peelPFin_toFin])
  rw [hP, peelGFin_toFin]

/-! ## 5. The transport of the state -/

/-- **The flat peel**: transport the state produced by `lstatePeelAbs` to the flat parameter set. -/
theorem lstateAbsFlat {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : SlotSet ι (fun _ => 1) → ℕ) {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ N D : ℕ) (A : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℤ → ℂ)
    (γ γ' : ℝ) (t' : ℕ) (s₀ : Slot ι (fun _ => 1))
    (h : LStateAbs (peelKω kω s₀) (peelP p M₁ M₂ A γ' t' s₀) M₁ M₂ N D
          (Finset.univ : Finset (PeelParam p M₁ M₂ A γ' t' s₀))
          (peelG p M₁ M₂ A γ' t' s₀ g) γ) :
    LStateAbs (peelKω kω s₀) (peelPFin p t' s₀) M₁ M₂ N D
      (shiftSetFin p M₁ M₂ A γ' t' s₀) (peelGFin t' g) γ := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  -- the box of the *original* ambient is nonempty (this is the fibre cardinality)
  have hbne : (paramBox (k := fun _ : ι => 1) M₂).Nonempty := by
    refine ⟨fun _ => 0, ?_⟩
    rw [paramBox, Fintype.mem_piFinset]
    intro s
    rw [Finset.mem_Ioo]
    constructor <;> omega
  have hbnz : ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr hbne)
  refine ⟨h0, h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the flat coefficient is nowhere zero
    intro s x hx
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
    rw [← hq, peelPFin_toFin]
    exact h6 s (peelSigma p M₁ M₂ A γ' t' s₀ q) (Finset.mem_univ _)
  · -- first shift bound
    intro s x hx
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
    rw [← hq, peelPFin_toFin]
    exact h7 s (peelSigma p M₁ M₂ A γ' t' s₀ q) (Finset.mem_univ _)
  · -- second shift bound
    intro s x hx
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
    rw [← hq, peelPFin_toFin]
    exact h8 s (peelSigma p M₁ M₂ A γ' t' s₀ q) (Finset.mem_univ _)
  · -- sup bound
    intro x hx y
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
    rw [← hq, peelGFin_toFin]
    exact h9 (peelSigma p M₁ M₂ A γ' t' s₀ q) (Finset.mem_univ _) y
  · -- support
    intro x hx
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
    rw [← hq, peelGFin_toFin]
    exact h10 (peelSigma p M₁ M₂ A γ' t' s₀ q) (Finset.mem_univ _)
  · -- the main averaged hypothesis
    let flatS : (Fin (n + 2 * t') → ℤ) → ℝ := fun x =>
      ∑ a' ∈ paramBox (k := fun _ : PeelSlot s₀ => 1) M₂,
        boxNorm (Fintype.card (FamIdx (peelKω kω s₀)))
          (fun j : Fin (Fintype.card (FamIdx (peelKω kω s₀))) =>
            pDirFamG (peelPFin p t' s₀) M₁ x a'
              ((Fintype.equivFin (FamIdx (peelKω kω s₀))).symm j))
          (symIcc N) (peelGFin t' g x)
    let nestS : PeelParam p M₁ M₂ A γ' t' s₀ → ℝ := fun q =>
      ∑ a' ∈ paramBox (k := fun _ : PeelSlot s₀ => 1) M₂,
        boxNorm (Fintype.card (FamIdx (peelKω kω s₀)))
          (fun j : Fin (Fintype.card (FamIdx (peelKω kω s₀))) =>
            pDirFamG (peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
              ((Fintype.equivFin (FamIdx (peelKω kω s₀))).symm j))
          (symIcc N) (peelG p M₁ M₂ A γ' t' s₀ g q)
    change γ ≤ ((shiftSetFin p M₁ M₂ A γ' t' s₀).card : ℝ)⁻¹
        * ((paramBox (k := fun _ : PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹
        * ∑ x ∈ shiftSetFin p M₁ M₂ A γ' t' s₀, flatS x
    have hpt : ∀ q, flatS (toFin p M₁ M₂ A γ' t' s₀ q)
        = nestS (peelSigma p M₁ M₂ A γ' t' s₀ q) := by
      intro q
      dsimp only [flatS, nestS]
      exact Finset.sum_congr rfl
        (fun a' _ => boxNorm_toFin_eq p M₁ M₂ A γ' t' s₀ g N kω q a')
    have hsigsum :
        ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, nestS (peelSigma p M₁ M₂ A γ' t' s₀ q)
          = ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, nestS q := by
      by_cases hn : n % 2 = 0
      · simp only [peelSigma, hn, if_true]
      · have hE : peelSigma p M₁ M₂ A γ' t' s₀ = peelSwap p M₁ M₂ A γ' t' s₀ := by
          funext q
          simp only [peelSigma, hn, if_false]
        rw [hE]
        simpa only [peelSwapEquiv_apply] using
          Equiv.sum_comp (peelSwapEquiv p M₁ M₂ A γ' t' s₀) nestS
    have hsumNest : ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, flatS (toFin p M₁ M₂ A γ' t' s₀ q)
        = ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, nestS q := by
      rw [Finset.sum_congr rfl (fun q _ => hpt q), hsigsum]
    have hsumFlat : ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, flatS (toFin p M₁ M₂ A γ' t' s₀ q)
        = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)
          * ∑ x : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀), flatS x.1 :=
      sum_toFin p M₁ M₂ A γ' t' s₀ flatS
    have hkey : ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)
          * (∑ x : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀), flatS x.1)
        = ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, nestS q := hsumFlat ▸ hsumNest
    have hmainFlat : (∑ x : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀), flatS x.1)
        = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹
          * ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, nestS q := by
      rw [← hkey, ← mul_assoc, inv_mul_cancel₀ hbnz, one_mul]
    have hcard : ((Finset.univ : Finset (PeelParam p M₁ M₂ A γ' t' s₀)).card : ℝ)
        = ((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)
          * ((shiftSetFin p M₁ M₂ A γ' t' s₀).card : ℝ) := by
      rw [Finset.card_univ, card_peelParam]
      push_cast
      ring
    have hAtt : (∑ x : ↥(shiftSetFin p M₁ M₂ A γ' t' s₀), flatS x.1)
        = ∑ x ∈ shiftSetFin p M₁ M₂ A γ' t' s₀, flatS x := Finset.sum_attach _ _
    rw [← hAtt, hmainFlat]
    have hgoal : ((shiftSetFin p M₁ M₂ A γ' t' s₀).card : ℝ)⁻¹
          * ((paramBox (k := fun _ : PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹
          * (((paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹
            * ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, nestS q)
        = ((Finset.univ : Finset (PeelParam p M₁ M₂ A γ' t' s₀)).card : ℝ)⁻¹
          * ((paramBox (k := fun _ : PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹
          * ∑ q : PeelParam p M₁ M₂ A γ' t' s₀, nestS q := by
      rw [hcard, mul_inv_rev]
      ring
    rw [hgoal]
    exact h11

/-- **The flat peel** (the statement delivered to the chain).  It is `lstatePeelAbs` followed by the
transport `lstateAbsFlat`. -/
theorem lstatePeelFin {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ)
    {n : ℕ} (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ N Dc : ℕ) (A : Finset (Fin n → ℤ)) (g : (Fin n → ℤ) → ℤ → ℂ)
    (γ γ' γ'' : ℝ) (t' : ℕ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (st : Work.Peluse.Prop36SW.LStateAbs kω p M₁ M₂ N Dc A g γ)
    (hγ' : 0 < γ') (hγ'' : 0 < γ'') (ht' : 1 ≤ t')
    (hL : 1 ≤ (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
    (hB : 1 ≤ Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
    (hconcl : γ'' ≤ (A.card : ℝ)⁻¹ *
        ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ∑ a ∈ A, ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω t'))
            (fun i => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
              ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω t')).symm i))
            (Work.Peluse.symIcc N) (g a)) :
    Work.Peluse.Prop36SW.LStateAbs (Work.Peluse.Prop36SW.peelKω kω s₀)
      (Work.Peluse.Prop36SW.peelPFin p t' s₀) M₁ M₂ (Work.Peluse.Prop36SW.peelN N Dc t' γ') Dc
      (Work.Peluse.Prop36SW.shiftSetFin p M₁ M₂ A γ' t' s₀)
      (Work.Peluse.Prop36SW.peelGFin t' g)
      (min ((((Work.Peluse.symIcc N).card : ℝ) /
              ((Work.Peluse.symIcc (Work.Peluse.Prop36SW.peelN N Dc t' γ')).card : ℝ)) ^
              (1 / (2 : ℝ) ^ (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))) *
            γ'' ^ (2 ^ Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω t'))) 1) :=
  lstateAbsFlat kω p M₁ M₂ (peelN N Dc t' γ') Dc A g
    (min ((((Work.Peluse.symIcc N).card : ℝ) /
            ((Work.Peluse.symIcc (peelN N Dc t' γ')).card : ℝ)) ^
            (1 / (2 : ℝ) ^ (Fintype.card (ShortIdx (k := fun _ : ι => 1) kω s₀))) *
          γ'' ^ (2 ^ Fintype.card (ConclIdx s₀ kω t'))) 1)
    γ' t' s₀
    (lstatePeelAbs kω p M₁ M₂ N Dc A g γ γ' γ'' t' s₀ st hγ' hγ'' ht' hL hB hconcl)

end

end Work.Peluse.Prop36SW
