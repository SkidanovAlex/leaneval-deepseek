import Mathlib.Tactic.Group
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.coboundary2_top_of_coboundary2_on_coprime_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A locally constant `2`-cocycle on a procyclically growing procyclic group is a coboundary

The main result of this file, `Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth`, is the
pro-cyclic case of the vanishing of the second continuous cohomology used in Shafarevich's
theorem: on a compact group `Γ` all of whose finite quotients are cyclic and which has open normal
subgroups of arbitrarily `p`-divisible index (`hbig`), every locally constant `2`-cocycle with
values in a finite `𝔽_p`-module is the coboundary of a locally constant `1`-cochain.

The two computational ingredients are proved first:

* `Work.SSGRoute.cob2_cyclic_of_sum_eq_zero`: a normalised `2`-cocycle on a *finite cyclic* group
  whose "norm" `∑_{i < #Q} c (x^i) x` along a generator vanishes is a coboundary;
* `Work.SSGRoute.cob2_sum_range_index_eq_zero`: the vanishing of that norm for the cocycle
  induced on `Γ ⧸ V` by a cocycle on `Γ` invariant under an open normal `R ≥ V` with `p ∣ [R : V]`.
-/

namespace Work.SSGRoute

open scoped Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

/-! ## A normalised `2`-cocycle on a finite cyclic group with vanishing norm -/

section FiniteCyclic

variable {Q N : Type} [Group Q] [Fintype Q] [AddCommGroup N]

/-- **A normalised `2`-cocycle on a finite cyclic group with vanishing norm is a coboundary.**

`Q` a finite group with `x : Q` generating it, `ρ : Q →* AddMonoid.End N` an action of `Q` on the
additive group `N` by additive endomorphisms, `c : Q → Q → N` a `2`-cocycle in the inhomogeneous
form `ρ g (c h l) - c (g*h) l + c g (h*l) - c g h = 0`, normalised (`c 1 h = 0`, `c g 1 = 0`) and
with vanishing norm `∑_{i < #Q} c (x^i) x = 0`.  Then `c` is a coboundary. -/
theorem cob2_cyclic_of_sum_eq_zero
    (ρ : Q →* AddMonoid.End N) (x : Q) (hx : ∀ y : Q, y ∈ Subgroup.zpowers x)
    (c : Q → Q → N)
    (hc : ∀ g h l : Q, ρ g (c h l) - c (g * h) l + c g (h * l) - c g h = 0)
    (hn1 : ∀ h : Q, c 1 h = 0) (hn2 : ∀ g : Q, c g 1 = 0)
    (hsum : (∑ i ∈ Finset.range (Fintype.card Q), c (x ^ i) x) = 0) :
    ∃ B : Q → N, ∀ g h : Q, c g h = ρ g (B h) - B (g * h) + B g := by
  classical
  set n : ℕ := Fintype.card Q with hn
  have hxn : x ^ n = 1 := by rw [hn]; exact pow_card_eq_one
  have hord : orderOf x = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hx, Nat.card_eq_fintype_card, hn]
  set S : ℕ → N := fun k => ∑ i ∈ Finset.range k, c (x ^ i) x with hS
  have hS_succ : ∀ k : ℕ, S (k + 1) = S k + c (x ^ k) x := by
    intro k
    simp only [hS, Finset.sum_range_succ]
  -- the cocycle identity makes the partial sums periodic with period `n`
  have hS_period : ∀ k : ℕ, S (k + n) = S k := by
    intro k
    have hterm : ∀ i : ℕ, c (x ^ (k + i)) x
        = ρ (x ^ k) (c (x ^ i) x) + c (x ^ k) (x ^ (i + 1)) - c (x ^ k) (x ^ i) := by
      intro i
      have h := hc (x ^ k) (x ^ i) x
      rw [← pow_add, ← pow_succ] at h
      have h2 : ρ (x ^ k) (c (x ^ i) x) + c (x ^ k) (x ^ (i + 1)) - c (x ^ k) (x ^ i)
          - c (x ^ (k + i)) x = 0 := by
        have e : (ρ (x ^ k) (c (x ^ i) x) + c (x ^ k) (x ^ (i + 1)) - c (x ^ k) (x ^ i)
            - c (x ^ (k + i)) x)
            = (ρ (x ^ k) (c (x ^ i) x) - c (x ^ (k + i)) x + c (x ^ k) (x ^ (i + 1))
              - c (x ^ k) (x ^ i)) := by abel
        rw [e, h]
      exact (sub_eq_zero.mp h2).symm
    have hsplit : S (k + n) = S k + ∑ i ∈ Finset.range n, c (x ^ (k + i)) x := by
      simp only [hS, Finset.sum_range_add]
    have hshift : (∑ i ∈ Finset.range n, c (x ^ k) (x ^ (i + 1)))
        = (∑ i ∈ Finset.range n, c (x ^ k) (x ^ i)) + c (x ^ k) (x ^ n)
          - c (x ^ k) (x ^ 0) := by
      have h1 := Finset.sum_range_sub (fun i : ℕ => c (x ^ k) (x ^ i)) n
      rw [Finset.sum_sub_distrib] at h1
      have h2 : (∑ i ∈ Finset.range n, c (x ^ k) (x ^ (i + 1)))
          = (c (x ^ k) (x ^ n) - c (x ^ k) (x ^ 0))
            + ∑ i ∈ Finset.range n, c (x ^ k) (x ^ i) :=
        sub_eq_iff_eq_add.mp h1
      rw [h2]; abel
    have hsum' : (∑ i ∈ Finset.range n, c (x ^ (k + i)) x) = 0 := by
      calc (∑ i ∈ Finset.range n, c (x ^ (k + i)) x)
          = ∑ i ∈ Finset.range n,
              (ρ (x ^ k) (c (x ^ i) x) + c (x ^ k) (x ^ (i + 1)) - c (x ^ k) (x ^ i)) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
        _ = ρ (x ^ k) (∑ i ∈ Finset.range n, c (x ^ i) x)
              + (∑ i ∈ Finset.range n, c (x ^ k) (x ^ (i + 1)))
              - (∑ i ∈ Finset.range n, c (x ^ k) (x ^ i)) := by
            rw [map_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        _ = ρ (x ^ k) (S n)
              + ((∑ i ∈ Finset.range n, c (x ^ k) (x ^ i)) + c (x ^ k) (x ^ n)
                  - c (x ^ k) (x ^ 0))
              - (∑ i ∈ Finset.range n, c (x ^ k) (x ^ i)) := by
            rw [hS, hshift]
        _ = ρ (x ^ k) (S n) + (c (x ^ k) (x ^ n) - c (x ^ k) (x ^ 0)) := by abel
        _ = 0 := by
            have hSn : S n = 0 := by rw [hS, hn]; exact hsum
            rw [hSn, map_zero, hxn, pow_zero, sub_self, add_zero]
    rw [hsplit, hsum', add_zero]
  have hS_step : ∀ k m : ℕ, S (k + n * m) = S k := by
    intro k m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : k + n * (m + 1) = (k + n * m) + n := by ring
      rw [h1, hS_period, ih]
  have hS_mod : ∀ k : ℕ, S k = S (k % n) := by
    intro k
    conv_lhs => rw [show k = (k % n) + n * (k / n) from by
      have := Nat.div_add_mod k n
      omega]
    rw [hS_step]
  have hS_eq : ∀ k j : ℕ, x ^ k = x ^ j → S k = S j := by
    intro k j hkj
    have hmod : k % n = j % n := by
      have h1 := pow_eq_pow_iff_modEq.mp hkj
      rw [hord] at h1
      exact h1
    rw [hS_mod k, hS_mod j, hmod]
  -- an exponent for every element of `Q`
  have hex : ∀ q : Q, ∃ k : ℕ, x ^ k = q := by
    intro q
    have h := (mem_zpowers_iff_mem_range_orderOf (x := x)).mp (hx q)
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    exact ⟨k, hk⟩
  let K : Q → ℕ := fun q => Classical.choose (hex q)
  have hK : ∀ q : Q, x ^ (K q) = q := fun q => Classical.choose_spec (hex q)
  let B : Q → N := fun q => - S (K q)
  have hB : ∀ j : ℕ, B (x ^ j) = - S j := by
    intro j
    show - S (K (x ^ j)) = - S j
    rw [hS_eq (K (x ^ j)) j (hK (x ^ j))]
  have hBx : B x = 0 := by
    have h1 : S (K x) = S 1 := hS_eq (K x) 1 (by simpa using hK x)
    show - S (K x) = 0
    rw [h1]
    simp only [hS, Finset.sum_range_one, pow_zero, hn1, neg_zero]
  -- the coboundary identity on the pairs `(g, x)`
  have hgen : ∀ g : Q, c g x = ρ g (B x) - B (g * x) + B g := by
    intro g
    have hmain : c (x ^ K g) x = ρ (x ^ K g) (B x) - B (x ^ K g * x) + B (x ^ K g) := by
      rw [hBx, map_zero, ← pow_succ, hB (K g + 1), hB (K g), hS_succ (K g)]
      abel
    simpa [hK g] using hmain
  set dB : Q → Q → N := fun g h => ρ g (B h) - B (g * h) + B g with hdB
  have hdB_coc : ∀ g h l : Q, ρ g (dB h l) - dB (g * h) l + dB g (h * l) - dB g h = 0 := by
    intro g h l
    have h1 : ρ (g * h) (B l) = ρ g (ρ h (B l)) := by
      have h2 := congrArg (fun f : AddMonoid.End N => f (B l)) (map_mul ρ g h)
      simpa [AddMonoid.End.coe_mul] using h2
    simp only [hdB]
    rw [map_add, map_sub, h1, mul_assoc]
    abel
  let u : Q → Q → N := fun g h => c g h - dB g h
  have hu_coc : ∀ g h l : Q, ρ g (u h l) - u (g * h) l + u g (h * l) - u g h = 0 := by
    intro g h l
    have h1 := hc g h l
    have h2 := hdB_coc g h l
    have hkey : ρ g (u h l) - u (g * h) l + u g (h * l) - u g h
        = (ρ g (c h l) - c (g * h) l + c g (h * l) - c g h)
          - (ρ g (dB h l) - dB (g * h) l + dB g (h * l) - dB g h) := by
      simp only [u]
      rw [map_sub]
      abel
    rw [hkey, h1, h2, sub_zero]
  have hu_gen : ∀ g : Q, u g x = 0 := by
    intro g
    show c g x - dB g x = 0
    rw [show dB g x = ρ g (B x) - B (g * x) + B g from rfl, hgen g, sub_self]
  have hu_step : ∀ g h : Q, u g (h * x) = u g h := by
    intro g h
    have h1 := hu_coc g h x
    rw [hu_gen h, hu_gen (g * h), map_zero] at h1
    have h2 : u g (h * x) - u g h = 0 := by simpa using h1
    exact sub_eq_zero.mp h2
  have hu_zero : ∀ g h : Q, u g h = 0 := by
    intro g h
    obtain ⟨j, hj⟩ := hex h
    have hall : ∀ j : ℕ, u g (x ^ j) = 0 := by
      intro j
      induction j with
      | zero =>
          have h1 := hu_step g 1
          rw [one_mul] at h1
          rw [pow_zero, ← h1]
          exact hu_gen g
      | succ j ih =>
          rw [pow_succ, hu_step g (x ^ j), ih]
    rw [← hj]
    exact hall j
  refine ⟨B, fun g h => ?_⟩
  have h1 : u g h = 0 := hu_zero g h
  rw [show u g h = c g h - dB g h from rfl] at h1
  rw [show dB g h = ρ g (B h) - B (g * h) + B g from rfl] at h1
  exact sub_eq_zero.mp h1

end FiniteCyclic

/-! ## The vanishing of the norm of the induced cocycle -/

section IndexSum

/-- The "norm" of a `2`-cocycle along a generator, over the index of `V`: if `V ≤ R`,
`p ∣ [R : V]`, `c` is invariant under right multiplication by `R` in the first variable and
`x ^ R.index ∈ R`, then `∑_{i < [Γ:V]} c (x^i) x = 0`.  Each block of `R.index` consecutive terms
has the common value `∑_{j < R.index} c (x^j) x`, and `[R:V]` is `0` in `ZMod p`. -/
theorem cob2_sum_range_index_eq_zero
    (p : ℕ) [Fact p.Prime] {Γ N : Type} [Group Γ] [AddCommGroup N] [Module (ZMod p) N]
    (R V : Subgroup Γ) (hVR : V ≤ R) (hpdvd : p ∣ (V.subgroupOf R).index)
    (c : Γ → Γ → N) (hRinv : ∀ g h : Γ, ∀ r ∈ R, c (r * g) h = c g h)
    (x : Γ) (hxR : x ^ R.index ∈ R) :
    (∑ i ∈ Finset.range V.index, c (x ^ i) x) = 0 := by
  classical
  have hblock : ∀ a j : ℕ, c (x ^ (a * R.index + j)) x = c (x ^ j) x := by
    intro a j
    have hxa : (x ^ R.index) ^ a ∈ R := Subgroup.pow_mem R hxR a
    rw [pow_add, mul_comm a R.index, pow_mul]
    exact hRinv _ _ _ hxa
  have hterm : ∀ K : ℕ, (∑ i ∈ Finset.range (K * R.index), c (x ^ i) x)
      = K • (∑ j ∈ Finset.range R.index, c (x ^ j) x) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih,
        Finset.sum_congr rfl (fun j _ => hblock K j), succ_nsmul]
  rw [← Subgroup.relIndex_mul_index hVR, hterm]
  have hzero : ((V.relIndex R : ℕ) : ZMod p) = 0 := by
    obtain ⟨t, ht⟩ := hpdvd
    have h1 : V.relIndex R = p * t := ht
    rw [h1, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) (V.relIndex R)
    (∑ j ∈ Finset.range R.index, c (x ^ j) x), hzero, zero_smul]

end IndexSum

/-! ## The main theorem -/

section Main

theorem isCoboundary2On_top_of_procyclicGrowth
    (p : ℕ) [Fact p.Prime] {Γ G N : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [Group G] [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction G N] [SMulCommClass G (ZMod p) N] [Finite N]
    (act : Γ →* G)
    (hcyc : ∀ (U : Subgroup Γ) [U.Normal], U.FiniteIndex → IsCyclic (Γ ⧸ U))
    (hker : ∃ U₀ : Subgroup Γ, IsOpen (U₀ : Set Γ) ∧ ∀ g ∈ U₀, ∀ n : N, act g • n = n)
    (hbig : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → U.Normal →
      ∃ V : Subgroup Γ, V ≤ U ∧ IsOpen (V : Set Γ) ∧ V.Normal ∧ p ∣ (V.subgroupOf U).index)
    (c : Γ → Γ → N) (hc : _root_.SSGRoute.IsCocycle2 act c)
    (hlc : _root_.SSGRoute.IsLocConst2 c) :
    _root_.SSGRoute.IsCoboundary2On act ⊤ c := by
  classical
  obtain ⟨U, hUopen, hUinv⟩ := hlc
  obtain ⟨U₀, hU₀open, hU₀triv⟩ := hker
  -- `γ := c 1 1`; the normalised cocycle `c₁ := c - δ (const γ)`.
  have hc11 : ∀ h : Γ, c 1 h = c 1 1 := by
    intro h
    have h1 := hc 1 1 h
    simp only [map_one, one_mul, one_smul] at h1
    have h2 : c 1 h - c 1 1 = 0 := by simpa using h1
    exact sub_eq_zero.mp h2
  have hcg1 : ∀ g : Γ, c g 1 = act g • c 1 1 := by
    intro g
    have h1 := hc g 1 1
    simp only [mul_one, one_mul] at h1
    have h2 : act g • c 1 1 - c g 1 = 0 := by simpa using h1
    exact (sub_eq_zero.mp h2).symm
  set γ : N := c 1 1 with hγ
  set c₁ : Γ → Γ → N := fun g h => c g h - act g • γ with hc₁def
  have hc₁_coc : SSGRoute.IsCocycle2 act c₁ := by
    have hcob := cob2_isCocycle2_sub (act := act) hc (cob2d_isCocycle act (fun _ : Γ => γ))
    intro g h l
    have h2 := hcob g h l
    simp only [hc₁def, cob2d, sub_add_cancel] at h2 ⊢
    exact h2
  have hc₁_lc : SSGRoute.IsLocConst2 c₁ := by
    refine ⟨U ⊓ U₀, ?_, ?_⟩
    · rw [Subgroup.coe_inf]; exact hUopen.inter hU₀open
    · intro g h u v hu hv
      have huU : u ∈ U := hu.1
      have hvU : v ∈ U := hv.1
      have huU₀ : u ∈ U₀ := hu.2
      show c (g * u) (h * v) - act (g * u) • γ = c g h - act g • γ
      rw [hUinv g h u v huU hvU, map_mul, mul_smul, hU₀triv u huU₀ γ]
  have hc₁_n1 : ∀ h : Γ, c₁ 1 h = 0 := by
    intro h
    show c 1 h - act 1 • γ = 0
    rw [map_one, one_smul, hγ, hc11 h, sub_self]
  have hc₁_n2 : ∀ g : Γ, c₁ g 1 = 0 := by
    intro g
    show c g 1 - act g • γ = 0
    rw [hcg1 g, hγ, sub_self]
  -- the normalised case
  have main : ∀ c' : Γ → Γ → N, SSGRoute.IsCocycle2 act c' → SSGRoute.IsLocConst2 c' →
      (∀ h : Γ, c' 1 h = 0) → (∀ g : Γ, c' g 1 = 0) → SSGRoute.IsCoboundary2On act ⊤ c' := by
    intro c' hc' hlc' hn1 hn2
    obtain ⟨U₁, hU₁open, hU₁inv⟩ := hlc'
    -- an open normal subgroup `R ≤ U₁ ⊓ U₀` under which `c'` is invariant
    have hKopen : IsOpen (((U₁ ⊓ U₀ : Subgroup Γ)) : Set Γ) := by
      rw [Subgroup.coe_inf]; exact hU₁open.inter hU₀open
    have hKclosed : IsClosed (((U₁ ⊓ U₀ : Subgroup Γ)) : Set Γ) :=
      Subgroup.isClosed_of_isOpen _ hKopen
    haveI hKfin : (U₁ ⊓ U₀ : Subgroup Γ).FiniteIndex := by
      rw [Subgroup.finiteIndex_iff_finite_quotient]
      exact Subgroup.quotient_finite_of_isOpen _ hKopen
    set R : Subgroup Γ := (U₁ ⊓ U₀).normalCore with hRdef
    haveI hRnorm : R.Normal := by rw [hRdef]; infer_instance
    have hRleK : R ≤ U₁ ⊓ U₀ := by rw [hRdef]; exact Subgroup.normalCore_le _
    haveI hRfin : R.FiniteIndex := by rw [hRdef]; infer_instance
    have hRopen : IsOpen (R : Set Γ) := by
      rw [hRdef]
      exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (Subgroup.normalCore_isClosed _ hKclosed)
    -- the growth hypothesis
    obtain ⟨V, hVleR, hVopen, hVnorm, hpdvd⟩ := hbig R hRopen hRnorm
    haveI hVnormI : V.Normal := hVnorm
    haveI hVfin : V.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff_finite_quotient]
      exact Subgroup.quotient_finite_of_isOpen V hVopen
    have hRinv1 : ∀ g h : Γ, ∀ r ∈ R, c' (g * r) h = c' g h := by
      intro g h r hr
      have h1 := hU₁inv g h r 1 (hRleK hr).1 U₁.one_mem
      simpa using h1
    have hRinv2 : ∀ g h : Γ, ∀ r ∈ R, c' g (h * r) = c' g h := by
      intro g h r hr
      have h1 := hU₁inv g h 1 r U₁.one_mem (hRleK hr).1
      simpa using h1
    have hRinv1L : ∀ g h : Γ, ∀ r ∈ R, c' (r * g) h = c' g h := by
      intro g h r hr
      have hconj : g⁻¹ * r * g ∈ R := by
        have hx := hRnorm.conj_mem r hr g⁻¹
        simpa using hx
      have h1 := hRinv1 g h (g⁻¹ * r * g) hconj
      rw [show g * (g⁻¹ * r * g) = r * g from by group] at h1
      exact h1
    have hVtriv : ∀ v ∈ V, ∀ n : N, act v • n = n := by
      intro v hv n
      exact hU₀triv v ((hRleK (hVleR hv)).2) n
    -- the quotient `Γ ⧸ V` is finite cyclic
    haveI hQfin : Finite (Γ ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVopen
    haveI hQft : Fintype (Γ ⧸ V) := Fintype.ofFinite _
    have hcycV : IsCyclic (Γ ⧸ V) := @hcyc V hVnormI hVfin
    obtain ⟨x, hxgen⟩ := hcycV.exists_generator
    -- the action of `Γ ⧸ V` on `N` and the induced cocycle
    letI : DistribMulAction Γ N := DistribMulAction.compHom N act
    let actEnd : Γ →* AddMonoid.End N := DistribMulAction.toAddMonoidEnd Γ N
    have hactEnd : ∀ (g : Γ) (n : N), actEnd g n = act g • n := by
      intro g n
      show act g • n = act g • n
      rfl
    have hVen : V ≤ actEnd.ker := by
      intro v hv
      ext n
      rw [hactEnd v n]
      simpa using hVtriv v hv n
    let ρ : (Γ ⧸ V) →* AddMonoid.End N := QuotientGroup.lift V actEnd hVen
    have hρ_mk : ∀ g : Γ, ρ (QuotientGroup.mk' V g) = actEnd g := fun g =>
      QuotientGroup.lift_mk' V hVen g
    set x₀ : Γ := Quotient.out x with hx₀def
    have hx₀mk : QuotientGroup.mk' V x₀ = x := by
      rw [hx₀def]; exact QuotientGroup.out_eq' x
    let cQ : (Γ ⧸ V) → (Γ ⧸ V) → N :=
      fun q q' => c' (Quotient.out q) (Quotient.out q')
    have hout : ∀ a : Γ, a⁻¹ * Quotient.out (QuotientGroup.mk' V a) ∈ V := by
      intro a
      refine QuotientGroup.eq.mp ?_
      have h1 : (↑(Quotient.out (QuotientGroup.mk' V a)) : Γ ⧸ V) = (↑a : Γ ⧸ V) := by
        rw [QuotientGroup.out_eq', QuotientGroup.mk'_apply]
      exact h1.symm
    have hcQ_mk : ∀ a b : Γ, cQ (QuotientGroup.mk' V a) (QuotientGroup.mk' V b) = c' a b := by
      intro a b
      have h1 : cQ (QuotientGroup.mk' V a) (QuotientGroup.mk' V b)
          = c' a (Quotient.out (QuotientGroup.mk' V b)) := by
        show c' (Quotient.out (QuotientGroup.mk' V a)) (Quotient.out (QuotientGroup.mk' V b))
          = c' a (Quotient.out (QuotientGroup.mk' V b))
        have hh := hRinv1 a (Quotient.out (QuotientGroup.mk' V b))
          (a⁻¹ * Quotient.out (QuotientGroup.mk' V a)) (hVleR (hout a))
        simpa using hh
      have h2 : c' a (Quotient.out (QuotientGroup.mk' V b)) = c' a b := by
        have hh := hRinv2 a b (b⁻¹ * Quotient.out (QuotientGroup.mk' V b)) (hVleR (hout b))
        simpa using hh
      rw [h1, h2]
    have hcQ_coc : ∀ g h l : Γ ⧸ V, ρ g (cQ h l) - cQ (g * h) l + cQ g (h * l) - cQ g h = 0 := by
      intro g h l
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V g
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V h
      obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective V l
      rw [← map_mul, ← map_mul, hcQ_mk b d, hcQ_mk (a * b) d, hcQ_mk a (b * d),
        hcQ_mk a b, hρ_mk a, hactEnd a (c' b d)]
      exact hc' a b d
    have hn1Q : ∀ h : Γ ⧸ V, cQ 1 h = 0 := by
      intro h
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V h
      have h1 : (1 : Γ ⧸ V) = QuotientGroup.mk' V (1 : Γ) := by rw [map_one]
      rw [h1, hcQ_mk, hn1]
    have hn2Q : ∀ g : Γ ⧸ V, cQ g 1 = 0 := by
      intro g
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V g
      have h1 : (1 : Γ ⧸ V) = QuotientGroup.mk' V (1 : Γ) := by rw [map_one]
      rw [h1, hcQ_mk, hn2]
    have hcQ_x : ∀ i : ℕ, cQ (x ^ i) x = c' (x₀ ^ i) x₀ := by
      intro i
      have h2 : x ^ i = QuotientGroup.mk' V (x₀ ^ i) := by
        rw [map_pow, hx₀mk]
      rw [h2, ← hx₀mk, hcQ_mk]
    have hsumQ : (∑ i ∈ Finset.range (Fintype.card (Γ ⧸ V)), cQ (x ^ i) x) = 0 := by
      have hcard : Fintype.card (Γ ⧸ V) = V.index := by
        rw [Fintype.card_eq_nat_card, Subgroup.index_eq_card]
      rw [Finset.sum_congr rfl (fun i _ => hcQ_x i), hcard]
      exact cob2_sum_range_index_eq_zero p R V hVleR hpdvd c' hRinv1L x₀
        (Subgroup.pow_index_mem R x₀)
    obtain ⟨B, hB⟩ := cob2_cyclic_of_sum_eq_zero ρ x hxgen cQ hcQ_coc hn1Q hn2Q hsumQ
    refine ⟨fun g => B (QuotientGroup.mk' V g), ⟨V, hVopen, ?_⟩, ?_⟩
    · intro g _ v hv _
      show B (QuotientGroup.mk' V (g * v)) = B (QuotientGroup.mk' V g)
      rw [map_mul, show QuotientGroup.mk' V v = 1 from (QuotientGroup.eq_one_iff v).mpr hv,
        mul_one]
    · intro g _ h _
      have h1 : c' g h = cQ (QuotientGroup.mk' V g) (QuotientGroup.mk' V h) := (hcQ_mk g h).symm
      rw [h1, hB (QuotientGroup.mk' V g) (QuotientGroup.mk' V h), hρ_mk g,
        hactEnd g (B (QuotientGroup.mk' V h)), ← map_mul]
      try rfl
  obtain ⟨B, hBloc, hBeq⟩ := main c₁ hc₁_coc hc₁_lc hc₁_n1 hc₁_n2
  refine ⟨fun g => B g + γ, ?_, ?_⟩
  · obtain ⟨W, hWopen, hWinv⟩ := hBloc
    refine ⟨W, hWopen, ?_⟩
    intro g _ u hu _
    show B (g * u) + γ = B g + γ
    rw [hWinv g (Subgroup.mem_top g) u hu (Subgroup.mem_top u)]
  · intro g _ h _
    show c g h = act g • (B h + γ) - (B (g * h) + γ) + (B g + γ)
    have h1 := hBeq g (Subgroup.mem_top g) h (Subgroup.mem_top h)
    have h3 : c g h = c₁ g h + act g • γ := by
      show c g h = (c g h - act g • γ) + act g • γ
      abel
    rw [h3, h1, smul_add]
    abel_nf

end Main

end Work.SSGRoute
