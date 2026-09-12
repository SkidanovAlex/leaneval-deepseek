import Mathlib
import Submission.Commons.LorentzianPolynomials.nuij_smoothing

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set Filter
open scoped Topology

namespace Commons.LorentzianPolynomials

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-- Each factor `(1 + θ·Xᵢ·∂ₛ)^d` is the identity at `θ = 0`. -/
lemma nuij_power_zero {n : ℕ} (i s : Fin n) (d : ℕ) (f : H n d) :
    nuij_power i s d 0 f = f := by
  induction d with
  | zero => simp [nuij_power]
  | succ d ih =>
      simp [nuij_power, nuij_deformEnd, ih]

/-- A fold of the identity factors at `θ = 0` is the identity. -/
lemma foldl_power_zero {n d : ℕ} (l : List (Fin n)) (s : Fin n) (f : H n d) :
    l.foldl (fun acc i => (nuij_power i s d 0) acc) f = f := by
  induction l generalizing f with
  | nil => simp
  | cons i l ih =>
      simp only [List.foldl_cons]
      rw [ih, nuij_power_zero]

/-- The value at `θ = 0` of the Nuij smoothing equals `f`. -/
lemma nuij_T_zero {n d : ℕ} (hn2 : 2 ≤ n) (f : H n d) :
    nuij_T hn2 0 f = f := by
  rw [nuij_T_eq_fold]
  exact foldl_power_zero (nuij_idx hn2) (nuij_s hn2) f

/-- iterate `x ↦ x + θ•L x` `d` times, jointly in `(θ, x)` -/
def hiter {n m : ℕ} (L : H n m →ₗ[ℝ] H n m) : ℕ → ℝ × H n m → H n m
  | 0, p => p.2
  | d + 1, p => hiter L d (p.1, p.2 + p.1 • (L p.2))

/-- the one-step deformation `(θ, x) ↦ x + θ • L x` is continuous -/
lemma oneStep_cont (n m : ℕ) (L : H n m →ₗ[ℝ] H n m) :
    Continuous (fun p : ℝ × H n m => p.2 + p.1 • (L p.2)) := by
  have hL : Continuous (fun p : ℝ × H n m => (L p.2 : H n m)) :=
    (IsModuleTopology.continuous_of_linearMap (R := ℝ) L).comp continuous_snd
  have hsmul : Continuous (fun p : ℝ × H n m => p.1 • (L p.2)) := by
    have h2 : Continuous (fun p : ℝ × H n m => (p.1, L p.2)) := continuous_fst.prodMk hL
    exact continuous_smul.comp h2
  exact continuous_add.comp (continuous_snd.prodMk hsmul)

/-- `hiter` implements the power `(id + θ•L)^d`. -/
lemma hiter_eq_pow {n m : ℕ} (L : H n m →ₗ[ℝ] H n m) (d : ℕ) (θ : ℝ) (x : H n m) :
    hiter L d (θ, x) = ((LinearMap.id + θ • L : Module.End ℝ (H n m)) ^ d) x := by
  induction d generalizing x with
  | zero => simp [hiter]
  | succ d ih =>
      rw [show hiter L (d+1) (θ,x) = hiter L d (θ, x + θ • (L x)) by rfl, ih]
      rw [pow_succ]
      rfl

/-- iterating the one-step deformation is continuous in `(θ, x)`. -/
lemma hiter_cont {n m : ℕ} (L : H n m →ₗ[ℝ] H n m) (d : ℕ) :
    Continuous (fun p : ℝ × H n m => hiter L d p) := by
  induction d with
  | zero => fun_prop [hiter]
  | succ d ih =>
      have hf1 : Continuous (fun p : ℝ × H n m => (p.1, p.2 + p.1 • (L p.2))) :=
        continuous_fst.prodMk (oneStep_cont n m L)
      convert ih.comp hf1 using 1
      funext p
      rfl

/-- joint continuity of one factor `(nuij_power i s d θ) x` in `(θ, x)` -/
lemma nuij_power_joint_cont {n d : ℕ} (i s : Fin n) :
    Continuous (fun p : ℝ × H n d => (nuij_power i s d p.1) p.2) := by
  induction d with
  | zero =>
      have h : ∀ p : ℝ × H n 0, (nuij_power i s 0 p.1) p.2 = p.2 := by
        intro p
        simp [nuij_power]
      exact continuous_snd.congr h
  | succ d ih =>
      let L : Module.End ℝ (H n (d + 1)) :=
        (nuij_mulXH d i).comp (nuij_pderivH d s)
      have hc : Continuous (fun p : ℝ × H n (d+1) => hiter L (d+1) p) := hiter_cont L (d+1)
      refine hc.congr ?_
      intro p
      rw [hiter_eq_pow]
      simp [nuij_power, L, nuij_deformEnd]

/-- continuity of an iterated fold over `nuij_power` in `θ`, with continuous initial value -/
lemma foldl_power_cont_aux {n d : ℕ} (l : List (Fin n)) (s : Fin n) :
    ∀ (h : ℝ → H n d), Continuous h →
      Continuous (fun θ : ℝ => l.foldl (fun acc i => (nuij_power i s d θ) acc) (h θ)) := by
  induction l with
  | nil => intro h hh; simpa using hh
  | cons i l ih =>
      intro h hh
      have hjoint : Continuous (fun p : ℝ × H n d => (nuij_power i s d p.1) p.2) :=
        nuij_power_joint_cont (n := n) (d := d) i s
      have hpair : Continuous (fun θ : ℝ => (θ, h θ)) := continuous_id.prodMk hh
      have hstep : Continuous (fun θ : ℝ => (nuij_power i s d θ) (h θ)) := by
        have hcomp : Continuous ((fun p : ℝ × H n d => (nuij_power i s d p.1) p.2) ∘
            (fun θ : ℝ => (θ, h θ))) := hjoint.comp hpair
        convert hcomp using 1
        funext θ
        rfl
      have hrest : Continuous (fun θ : ℝ =>
          l.foldl (fun acc j => (nuij_power j s d θ) acc) ((nuij_power i s d θ) (h θ))) :=
        ih _ hstep
      simpa [List.foldl_cons] using hrest

/-- a fold of `nuij_power` over a fixed list, applied to a fixed vector, is continuous in `θ` -/
lemma fold_power_cont {n d : ℕ} (l : List (Fin n)) (s : Fin n) (f : H n d) :
    Continuous (fun θ : ℝ => l.foldl (fun acc i => (nuij_power i s d θ) acc) f) := by
  simpa using foldl_power_cont_aux l s (fun _ : ℝ => f) continuous_const

/-- the Nuij smoothing is continuous in the parameter `θ`. -/
lemma nuij_T_cont {n d : ℕ} (hn2 : 2 ≤ n) (f : H n d) :
    Continuous (fun θ : ℝ => nuij_T hn2 θ f) := by
  refine (fold_power_cont (nuij_idx hn2) (nuij_s hn2) f).congr ?_
  intro θ
  rw [nuij_T_eq_fold]

/-- `1/(k+1) → 0` as `k → ∞`. -/
lemma tendsto_one_div_succ :
    Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1 : ℝ)) atTop (𝓝 0) := by
  simpa [Nat.cast_add, Nat.cast_one, add_comm] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The interior density statement, assembled from `nuij_smoothing` by sending `θ → 0`.
The proof needs: continuity of `θ ↦ nuij_T hn2 θ f`, the value at `θ = 0` equal to `f`,
and the sequence `1/(k+1) → 0`. -/
theorem lp_density_asm (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    (L n d ∩ P n d) ⊆ closure (Ŀ n d) := by
  intro f hf
  let θk : ℕ → ℝ := fun k => (1 : ℝ) / (k + 1 : ℝ)
  have hθk_pos : ∀ k, 0 < θk k := by
    intro k
    dsimp [θk]
    positivity
  have hmem : ∀ k, nuij_T (n := n) (d := d) hn2 (θk k) f ∈ Ŀ n d := by
    intro k
    exact nuij_smoothing n d hn2 hd (θk k) (hθk_pos k) f hf
  have htend0 : Tendsto θk atTop (𝓝 0) := by
    simpa [θk] using tendsto_one_div_succ
  have htend : Tendsto (fun k : ℕ => nuij_T (n := n) (d := d) hn2 (θk k) f) atTop (𝓝 f) := by
    have hc : Tendsto (fun θ : ℝ => nuij_T hn2 θ f) (𝓝 (0 : ℝ))
        (𝓝 (nuij_T hn2 0 f)) :=
      (nuij_T_cont hn2 f).tendsto 0
    rw [nuij_T_zero hn2 f] at hc
    exact hc.comp htend0
  exact mem_closure_of_tendsto htend (Filter.Eventually.of_forall hmem)

end
end Commons.LorentzianPolynomials
