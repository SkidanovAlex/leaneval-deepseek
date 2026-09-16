import Submission.ZagierHoffmanProof.AmbZeta

/-!
# The valuation of the transfer `ambInfHom : K_∞ → Ambient F`, and Step 3's divisibility

Step 3 of the proof of Theorem B (Ngo Dac, *On Zagier–Hoffman's conjectures in positive
characteristic*, Annals 194 (2021), §5.3) converts the rationality statement `f_𝔱(θ) ∈ K` of Step 2
into the divisibility `(q-1) ∣ (w - w(𝔱))` of the weight of the relevant suffix.  Via the bridge
(4.2), `f_𝔱(θ) = a_i·Γ_𝔰·ζ_A(𝔰)/π̃^{w(𝔰)}` with `a_i ∈ K^×`, `Γ_𝔰 ∈ K` and `𝔰` the suffix, so the
divisibility is a statement about **value groups**:

* `v (π̃^m) = exp (q m)` (`Step3Val.v_ambPiTilde_pow`);
* `v x ∈ exp ((q-1)ℤ)` for every `x ∈ K = F_q(θ)` (`Step3Val.v_mem_ambK`);
* `v x ∈ exp ((q-1)ℤ)` for every `x ∈ K_∞ = F_q((1/θ))` — **this file**, `v_ambInfHom_mem_pred`.

The last statement is what this file adds: the completion `K_∞` is not a subring of `Ambient F`
containing `θ` in the naive sense, but its image under `ambInfHom` is contained in the closed
subring of elements whose valuation lies in `exp ((q-1)ℤ)`; since `K_∞` is the completion of
`K = F_q(θ)` and `ambInfHom` is continuous, the image of the whole completion is contained in the
*closure* of the image of `K`, and the value-group property is inherited from the dense image by
`Valued.locally_const`.  (`ambInfHom` is injective because it is a ring homomorphism out of a
field into a nontrivial ring.)

## Main results

* `ambInfHom_injective`.
* `ambInfHom_mem_closure`: the image lies in the closure of `K = F_q(θ)`.
* ★★★ `v_ambInfHom_mem_pred`: `v (ambInfHom x) ∈ exp ((q-1)ℤ)` for `x ≠ 0`.
* ★★★ `dvd_pred_of_v_exp_pow`: `(q-1) ∣ m` when the value group member `exp (q m)` of a power of
  `π̃` is a quotient of two `exp ((q-1)ℤ)`-values (the exact form Step 3 produces).
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology RatFunc.CompletionAtInfty

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. Injectivity and the closure of the image -/

/-- `ambInfHom` is injective: it is a ring homomorphism from the field `K_∞` into the nontrivial
ring `Ambient F`. -/
theorem ambInfHom_injective : Function.Injective (ambInfHom F) := by
  refine (RingHom.injective_iff_ker_eq_bot _).mpr ?_
  rcases Ideal.eq_bot_or_top (RingHom.ker (ambInfHom F)) with h | h
  · exact h
  · exact absurd h (RingHom.ker_ne_top _)

/-- The image of `ambInfHom` is contained in the closure of the image of `K = F_q(θ)`. -/
theorem ambInfHom_mem_closure (x : RatFunc.CompletionAtInfty F) :
    ambInfHom F x ∈ closure (Set.range (ambKHomAmb F)) := by
  haveI : Valued (RatFunc F) ℤᵐ⁰ := RatFunc.inftyValued F
  have hdense : DenseRange (fun y : RatFunc F => (y : RatFunc.CompletionAtInfty F)) :=
    UniformSpace.Completion.denseRange_coe
  have hmem : x ∈ closure
      (Set.range (fun y : RatFunc F => (y : RatFunc.CompletionAtInfty F))) := by
    rw [hdense.closure_eq]; trivial
  have hsub := image_closure_subset_closure_image (continuous_ambInfHom F)
    (s := Set.range (fun y : RatFunc F => (y : RatFunc.CompletionAtInfty F)))
  have h2 := hsub (Set.mem_image_of_mem (ambInfHom F) hmem)
  have hset : (ambInfHom F) ''
      (Set.range (fun y : RatFunc F => (y : RatFunc.CompletionAtInfty F)))
      = Set.range (ambKHomAmb F) := by
    ext z
    constructor
    · rintro ⟨c, ⟨d, hd⟩, hcz⟩
      refine ⟨d, ?_⟩
      rw [← hd] at hcz
      rw [← hcz]
      exact (ambInfHom_coe F d).symm
    · rintro ⟨c, hcz⟩
      refine ⟨(c : RatFunc.CompletionAtInfty F), ⟨c, rfl⟩, ?_⟩
      rw [ambInfHom_coe]
      exact hcz
  rwa [hset] at h2

/-! ## §2. The value group of the image -/

/-- **Every element of the closure of `K = F_q(θ)` (inside `Ambient F`) has its valuation in
`exp ((q-1)ℤ)`, unless it is zero.**  The proof is the "closest approximation" argument: for a
nonzero `y` in the closure, the neighbourhood `{z | v z = v y}` of `y` (`Valued.locally_const`)
meets `K`, and `K`'s nonzero elements have valuation `exp ((q-1)·intDegree)`. -/
theorem v_mem_closure_ambKHomAmb {y : Ambient F}
    (hy : y ∈ closure (Set.range (ambKHomAmb F))) :
    y = 0 ∨ ∃ k : ℤ, Valued.v y = WithZero.exp (((Nat.card F : ℚ) - 1) * (k : ℚ)) := by
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  refine Or.inr ?_
  have hv0 : Valued.v y ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact hy0
  have hnb : {z : Ambient F | Valued.v z = Valued.v y} ∈ 𝓝 y := Valued.locally_const hv0
  obtain ⟨w, hw1, hw2⟩ := (mem_closure_iff_nhds.mp hy) _ hnb
  obtain ⟨c, hc⟩ := hw2
  simp only [Set.mem_ofPred_eq] at hw1
  rw [← hc] at hw1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, Valuation.map_zero] at hw1
    exact hv0 hw1.symm
  exact ⟨c.intDegree, by rw [← hw1]; exact v_ambKEquiv F c hc0⟩

/-- ★★★ **The valuation of `ambInfHom x` lies in `exp ((q-1)ℤ)`**: the transfer of the value
group computed on `K = F_q(θ)` (`Step3Val.v_mem_ambK`) extends to the completion `K_∞`. -/
theorem v_ambInfHom_mem_pred (x : RatFunc.CompletionAtInfty F) (hx : x ≠ 0) :
    ∃ k : ℤ, Valued.v (ambInfHom F x) = WithZero.exp (((Nat.card F : ℚ) - 1) * (k : ℚ)) := by
  rcases v_mem_closure_ambKHomAmb F (ambInfHom_mem_closure F x) with h | h
  · exact absurd (ambInfHom_injective F (h.trans (map_zero _).symm)) hx
  · exact h

/-! ## §3. The refined `π̃`-divisibility of Step 3 -/

/-- **Step 3's arithmetic, in the form produced by the bridge**: if the value of the element `y`
equals `exp (q m)` (for instance `y = π̃^m`, whose value is `exp (q m)` by
`Step3Val.v_ambPiTilde_pow`) and if that value also lies in `exp ((q-1)ℤ)` — which is what the
bridge gives, the numerator being an element of `K_∞` and the denominator an element of `K` — then
`(q-1) ∣ m`. -/
theorem dvd_pred_of_v_eq_exp {m : ℕ} {y : Ambient F}
    (h : Valued.v y = WithZero.exp ((Nat.card F : ℚ) * (m : ℚ)))
    (hy : ∃ k : ℤ, Valued.v y = WithZero.exp (((Nat.card F : ℚ) - 1) * (k : ℚ))) :
    (Nat.card F - 1) ∣ m := by
  obtain ⟨k, hk⟩ := hy
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  have hq1 : 1 ≤ Nat.card F := by omega
  have hexp : (Nat.card F : ℚ) * (m : ℚ) = ((Nat.card F : ℚ) - 1) * (k : ℚ) :=
    WithZero.exp_injective (h.symm.trans hk)
  have hcast : (((Nat.card F - 1 : ℕ)) : ℚ) = (Nat.card F : ℚ) - 1 := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
  have hZ : (((Nat.card F - 1 : ℕ)) : ℤ) * k = ((Nat.card F : ℕ) : ℤ) * ((m : ℕ) : ℤ) := by
    have h2 : ((((Nat.card F - 1 : ℕ)) : ℤ) * k : ℚ)
        = ((((Nat.card F : ℕ)) : ℤ) * ((m : ℕ) : ℤ) : ℚ) := by
      push_cast
      rw [hcast]
      exact hexp.symm
    exact_mod_cast h2
  have hdivZ : (((Nat.card F - 1 : ℕ)) : ℤ)
      ∣ ((((Nat.card F : ℕ)) : ℤ) * ((m : ℕ) : ℤ)) := ⟨k, hZ.symm⟩
  have hdivN : (Nat.card F - 1) ∣ (Nat.card F) * m := by
    have h3 : (((Nat.card F - 1 : ℕ)) : ℤ) ∣ ((((Nat.card F) * m : ℕ)) : ℤ) := by
      rw [Nat.cast_mul]
      exact hdivZ
    exact_mod_cast h3
  have hcop : Nat.Coprime (Nat.card F - 1) (Nat.card F) :=
    (Nat.coprime_self_sub_left hq1).mpr (Nat.coprime_one_left _)
  exact hcop.dvd_of_dvd_mul_left hdivN

/-- The form in which the bridge is applied: the `π̃`-power's value `exp (q m)` (times any factor
with value in `exp ((q-1)ℤ)`) forces `(q-1) ∣ m`. -/
theorem dvd_pred_of_v_eq_exp_mul {m : ℕ} {y u v : Ambient F}
    (hy : Valued.v y = WithZero.exp ((Nat.card F : ℚ) * (m : ℚ)))
    (hu : ∃ k : ℤ, Valued.v u = WithZero.exp (((Nat.card F : ℚ) - 1) * (k : ℚ)))
    (hv : ∃ k : ℤ, Valued.v v = WithZero.exp (((Nat.card F : ℚ) - 1) * (k : ℚ)))
    (hv0 : v ≠ 0) (h : y * v = u) : (Nat.card F - 1) ∣ m := by
  have hvv : Valued.v v ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact hv0
  have hyv : Valued.v y = Valued.v u / Valued.v v := by
    rw [eq_div_iff hvv, ← map_mul, h]
  refine dvd_pred_of_v_eq_exp F hy ?_
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  refine ⟨a - b, ?_⟩
  rw [hyv, ha, hb, ← WithZero.exp_sub]
  congr 1
  push_cast
  ring

end ZagierHoffmanPositiveChar
