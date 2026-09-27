import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.commutingPairDependent
import Submission.Work.Mostow.pairStabCocycleDiscrete
import Submission.Work.Mostow.geomFiniteBusemann

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

noncomputable section

variable {n : ℕ}

/-- If `x` commutes with `gp`, both boundary points `ξ ≠ η` are fixed by `gp`, and these are the
only boundary points fixed by `gp`, then `x ^ 2` fixes both `ξ` and `η`.

Indeed `x` maps fixed points of `gp` to fixed points of `gp`, so `x` permutes `{ξ,η}`; a
permutation of a two-element set is fixed by its square. -/
lemma bd_sq_fix_of_commute (hP : POBasic n) (x gp : PO n 1) {ξ η : E n}
    (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η)
    (hgpξ : bd gp ξ = ξ) (hgpη : bd gp η = η)
    (hno : ∀ ζ : E n, ζ ∈ Sph n → bd gp ζ = ζ → ζ = ξ ∨ ζ = η)
    (hcomm : x * gp = gp * x) :
    bd (x ^ 2) ξ = ξ ∧ bd (x ^ 2) η = η := by
  have hmemξ : bd x ξ ∈ Sph n := hP.bd_mem x ξ hξ
  have hmemη : bd x η ∈ Sph n := hP.bd_mem x η hη
  have hfixξ : bd gp (bd x ξ) = bd x ξ := by
    calc bd gp (bd x ξ) = bd (gp * x) ξ := (hP.bd_mul gp x ξ hξ).symm
      _ = bd (x * gp) ξ := by rw [← hcomm]
      _ = bd x (bd gp ξ) := hP.bd_mul x gp ξ hξ
      _ = bd x ξ := by rw [hgpξ]
  have hfixη : bd gp (bd x η) = bd x η := by
    calc bd gp (bd x η) = bd (gp * x) η := (hP.bd_mul gp x η hη).symm
      _ = bd (x * gp) η := by rw [← hcomm]
      _ = bd x (bd gp η) := hP.bd_mul x gp η hη
      _ = bd x η := by rw [hgpη]
  have h1 : bd x ξ = ξ ∨ bd x ξ = η := hno (bd x ξ) hmemξ hfixξ
  have h2 : bd x η = ξ ∨ bd x η = η := hno (bd x η) hmemη hfixη
  -- `bd x` is injective on `Sph n`
  have hinj : ∀ a ∈ Sph n, ∀ b ∈ Sph n, bd x a = bd x b → a = b := by
    intro a ha b hb hab
    have h1' : a = bd x⁻¹ (bd x a) := by
      rw [← hP.bd_mul x⁻¹ x a ha, inv_mul_cancel, hP.bd_one a ha]
    have h2' : b = bd x⁻¹ (bd x b) := by
      rw [← hP.bd_mul x⁻¹ x b hb, inv_mul_cancel, hP.bd_one b hb]
    rw [h1', h2', hab]
  have hne' : bd x ξ ≠ bd x η := fun h => hne (hinj ξ hξ η hη h)
  have hx2ξ : bd (x ^ 2) ξ = bd x (bd x ξ) := by
    rw [pow_two, hP.bd_mul x x ξ hξ]
  have hx2η : bd (x ^ 2) η = bd x (bd x η) := by
    rw [pow_two, hP.bd_mul x x η hη]
  constructor
  · rw [hx2ξ]
    rcases h1 with h | h
    · rw [h]; exact h
    · rw [h]
      rcases h2 with h2' | h2'
      · rw [h2']
      · exact absurd (by rw [h, h2'] : bd x ξ = bd x η) hne'
  · rw [hx2η]
    rcases h2 with h | h
    · rw [h]
      rcases h1 with h1' | h1'
      · exact absurd (by rw [h1', h] : bd x ξ = bd x η) hne'
      · rw [h1']
    · rw [h]; exact h

theorem cuspLoxContra (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Λ : Subgroup (PO n 1)) (hΛ : HypLattice Λ) (γ : Λ) (k : ℕ) (hk : 0 < k) (a b : Λ)
    (ha : a * γ ^ k = γ ^ k * a) (hb : b * γ ^ k = γ ^ k * b) (hab : a * b = b * a)
    (hind : ∀ i j : ℤ, (a : PO n 1) ^ i * (b : PO n 1) ^ j = 1 → i = 0 ∧ j = 0)
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hξη : ξ ≠ η)
    (hξfix : bd ((γ : PO n 1) ^ k) ξ = ξ) (hηfix : bd ((γ : PO n 1) ^ k) η = η)
    (hβ : busemann ξ (((γ : PO n 1) ^ k) • (0 : E n)) ≠ 0)
    (hno3 : ∀ ζ : E n, ζ ∈ Sph n → bd ((γ : PO n 1) ^ k) ζ = ζ → ζ = ξ ∨ ζ = η)
    (hpair : ∃ p : E n, ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
        hdist p (g • p) = |busemann ξ (g • (0 : E n))|)
    (hdis : ∃ c : ℝ, ∀ γ' : Λ, bd (γ' : PO n 1) ξ = ξ → bd (γ' : PO n 1) η = η →
        ∃ m : ℤ, busemann ξ ((γ' : PO n 1) • (0 : E n)) = m * c)
    (hker : {γ' : Λ | bd (γ' : PO n 1) ξ = ξ ∧ bd (γ' : PO n 1) η = η ∧
        busemann ξ ((γ' : PO n 1) • (0 : E n)) = 0}.Finite) : False := by
  have hP : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  -- commutation with `(γ : PO) ^ k`, transported to `PO n 1`
  have hcommA : (a : PO n 1) * (γ : PO n 1) ^ k = (γ : PO n 1) ^ k * (a : PO n 1) := by
    have h1 := congrArg (fun z : Λ => (z : PO n 1)) ha
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using h1
  have hcommB : (b : PO n 1) * (γ : PO n 1) ^ k = (γ : PO n 1) ^ k * (b : PO n 1) := by
    have h1 := congrArg (fun z : Λ => (z : PO n 1)) hb
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using h1
  -- `a ^ 2` and `b ^ 2` fix `ξ` and `η`
  have hfixA := bd_sq_fix_of_commute hP (a : PO n 1) ((γ : PO n 1) ^ k) hξ hη hξη
    hξfix hηfix hno3 hcommA
  have hfixB := bd_sq_fix_of_commute hP (b : PO n 1) ((γ : PO n 1) ^ k) hξ hη hξη
    hξfix hηfix hno3 hcommB
  -- the pair stabiliser of `(ξ,η)` in `Λ`
  let S : Subgroup Λ := pairStab hA Λ ξ η hξ hη
  have haS : a ^ 2 ∈ S := by
    change bd (((a ^ 2 : Λ)) : PO n 1) ξ = ξ ∧ bd (((a ^ 2 : Λ)) : PO n 1) η = η
    simpa only [Subgroup.coe_pow] using hfixA
  have hbS : b ^ 2 ∈ S := by
    change bd (((b ^ 2 : Λ)) : PO n 1) ξ = ξ ∧ bd (((b ^ 2 : Λ)) : PO n 1) η = η
    simpa only [Subgroup.coe_pow] using hfixB
  -- the additive homomorphism `β γ = busemann ξ (γ • 0)` on `S`
  let β : S →* Multiplicative ℝ :=
    { toFun := fun s => Multiplicative.ofAdd (beta s)
      map_one' := by
        show Multiplicative.ofAdd (beta (1 : S)) = 1
        rw [beta_one (hA := hA)]
        rfl
      map_mul' := by
        intro s t
        show Multiplicative.ofAdd (beta (s * t))
          = Multiplicative.ofAdd (beta s) * Multiplicative.ofAdd (beta t)
        rw [beta_add (hA := hA) (hI := hI) s t]
        rfl }
  obtain ⟨c, hc⟩ := hdis
  have hcβ : ∀ s : S, ∃ m : ℤ, Multiplicative.toAdd (β s) = (m : ℝ) * c := by
    intro s
    obtain ⟨m, hm⟩ := hc (s : Λ) s.2.1 s.2.2
    refine ⟨m, ?_⟩
    have hval : Multiplicative.toAdd (β s) = beta s := rfl
    rw [hval, beta]
    exact hm
  have hkerFin : {s : S | β s = 1}.Finite := by
    have hsub : {s : S | β s = 1} ⊆ (fun s : S => (s : Λ)) ⁻¹'
        {γ' : Λ | bd (γ' : PO n 1) ξ = ξ ∧ bd (γ' : PO n 1) η = η ∧
          busemann ξ ((γ' : PO n 1) • (0 : E n)) = 0} := by
      intro s hs
      refine ⟨s.2.1, s.2.2, ?_⟩
      have hh : beta s = 0 := by
        have h1 : Multiplicative.toAdd (β s) = Multiplicative.toAdd (1 : Multiplicative ℝ) :=
          congrArg Multiplicative.toAdd hs
        rw [show Multiplicative.toAdd (1 : Multiplicative ℝ) = (0 : ℝ) from rfl] at h1
        rwa [show Multiplicative.toAdd (β s) = beta s from rfl] at h1
      simpa only [beta] using hh
    exact (hker.preimage (fun x _ y _ h => Subtype.ext h)).subset hsub
  -- pure group theory: a relation `a ^ i * b ^ j = 1` exists
  obtain ⟨i, j, hij, hrel⟩ :=
    commutingPairDependent S β c hcβ hkerFin a b hab haS hbS
  have hrelPO : (a : PO n 1) ^ i * (b : PO n 1) ^ j = 1 := by
    have h1 := congrArg (fun z : Λ => (z : PO n 1)) hrel
    simpa only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one] using h1
  obtain ⟨hi, hj⟩ := hind i j hrelPO
  rcases hij with h | h
  · exact h hi
  · exact h hj

end

end Work.Mostow
