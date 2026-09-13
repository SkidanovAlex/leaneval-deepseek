import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_complements
import Submission.Commons.LinearAlgebra.Submodule.card_complements_between
import Submission.Commons.LinearAlgebra.LinearMap.finrank_comap_eq
import Submission.Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le

set_option linter.style.haveILetI false
set_option linter.ambiguousOpen false

namespace Commons.LinearAlgebra.LinearMap

open Module LinearMap

noncomputable section

/-- If `W ⊔ (image of KX in W₂) = W₂` then every element of `↥W₂` is the sum of an element of `↥W`
(embedded via `inclusion`) and an element of `KX`. -/
lemma exists_inclusion_add_of_mem_sup {K : Type*} [Field K] {C : Type*} [AddCommGroup C] [Module K C]
    (W W₂ : Submodule K C) (hWW : W ≤ W₂) (KX : Submodule K ↥W₂)
    (h : W ⊔ Submodule.map W₂.subtype KX = W₂) (x : ↥W₂) :
    ∃ (w : ↥W) (k : KX), x = Submodule.inclusion hWW w + (k : ↥W₂) := by
  have hx : (x : C) ∈ W ⊔ Submodule.map W₂.subtype KX := by rw [h]; exact x.2
  rw [Submodule.mem_sup] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := hx
  rw [Submodule.mem_map] at hz
  obtain ⟨k, hk, hkz⟩ := hz
  refine ⟨⟨y, hy⟩, ⟨k, hk⟩, ?_⟩
  apply Subtype.ext
  show (x : C) = y + (k : C)
  rw [← hyz, ← hkz]
  rfl

/-- If `W ⊔ (image of the kernel of `X` in `W₂) = W₂` then `range X` is already the range of the
restriction of `X` to `W`. -/
lemma range_comp_inclusion_eq_of_sup_ker {K : Type*} [Field K] {C N : Type*} [AddCommGroup C]
    [Module K C] [AddCommGroup N] [Module K N] (W W₂ : Submodule K C) (hWW : W ≤ W₂)
    (X : ↥W₂ →ₗ[K] N) (h : W ⊔ Submodule.map W₂.subtype X.ker = W₂) :
    (X.comp (Submodule.inclusion hWW)).range = X.range := by
  apply le_antisymm
  · exact LinearMap.range_comp_le_range _ _
  · intro y hy
    rw [LinearMap.mem_range] at hy ⊢
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨w, k, hwk⟩ := exists_inclusion_add_of_mem_sup W W₂ hWW X.ker h x
    refine ⟨w, ?_⟩
    rw [hwk, map_add, LinearMap.mem_ker.mp k.2, add_zero]
    rfl

/-- If the compression of `X` to `W` equals `Z` and `W ⊔ ker X = W₂`, then `q` maps `range X`
onto `range Z`. -/
lemma map_range_eq_of_comp_inclusion {K : Type*} [Field K] {C N N' : Type*} [AddCommGroup C]
    [Module K C] [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (W W₂ : Submodule K C) (hWW : W ≤ W₂) (X : ↥W₂ →ₗ[K] N) (q : N →ₗ[K] N')
    (Z : ↥W →ₗ[K] N') (h : W ⊔ Submodule.map W₂.subtype X.ker = W₂)
    (hcomp : ∀ w : ↥W, q (X (Submodule.inclusion hWW w)) = Z w) :
    Submodule.map q X.range = Z.range := by
  rw [← range_comp_inclusion_eq_of_sup_ker W W₂ hWW X h, ← LinearMap.range_comp]
  congr 1
  ext w
  exact hcomp w

/-- If `A ⊓ ker q = ⊥` and `q` maps `A` onto `R`, then `finrank A = finrank R` and
`A ⊔ ker q = q ⁻¹' R`. -/
lemma finrank_eq_and_sup_ker_eq_comap {K : Type*} [Field K] {N N' : Type*} [AddCommGroup N]
    [Module K N] [AddCommGroup N'] [Module K N'] [FiniteDimensional K N] [FiniteDimensional K N']
    (q : N →ₗ[K] N') (A : Submodule K N) (R : Submodule K N')
    (hA : Submodule.map q A = R) (hdisj : A ⊓ q.ker = ⊥) :
    Module.finrank K ↥A = Module.finrank K ↥R ∧
      A ⊔ q.ker = Submodule.comap q R := by
  have hAle : A ≤ Submodule.comap q R := by
    rw [← Submodule.map_le_iff_le_comap, hA]
  have hkerle : q.ker ≤ Submodule.comap q R := by
    intro x hx
    rw [Submodule.mem_comap]
    rw [LinearMap.mem_ker] at hx
    rw [hx]
    exact R.zero_mem
  have hsup_le : A ⊔ q.ker ≤ Submodule.comap q R := sup_le hAle hkerle
  have hRle : Module.finrank K ↥R ≤ Module.finrank K ↥A := by
    rw [← hA]; exact Submodule.finrank_map_le q A
  have hfin_sup : Module.finrank K ↥(A ⊔ q.ker) = Module.finrank K ↥A + Module.finrank K ↥q.ker := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A q.ker
    rw [hdisj, finrank_bot, add_zero] at h
    exact h
  have hcomap : Module.finrank K ↥(Submodule.comap q R) =
      Module.finrank K ↥q.ker + Module.finrank K ↥(R ⊓ q.range) :=
    Commons.LinearAlgebra.LinearMap.finrank_comap_eq q R
  have hRinf : Module.finrank K ↥(R ⊓ q.range) ≤ Module.finrank K ↥R :=
    Submodule.finrank_mono inf_le_left
  have hAle' : Module.finrank K ↥A ≤ Module.finrank K ↥R := by
    have h1 : Module.finrank K ↥A = Module.finrank K ↥(A ⊔ q.ker) - Module.finrank K ↥q.ker := by omega
    have h2 : Module.finrank K ↥(A ⊔ q.ker) ≤ Module.finrank K ↥(Submodule.comap q R) :=
      Submodule.finrank_mono hsup_le
    have h3 : Module.finrank K ↥(Submodule.comap q R) ≤
        Module.finrank K ↥q.ker + Module.finrank K ↥R := by rw [hcomap]; omega
    omega
  refine ⟨le_antisymm hAle' hRle, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq hsup_le
  rw [hfin_sup, hcomap]
  have hRrange : R ≤ q.range := by
    intro x hx
    rw [← hA, Submodule.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact LinearMap.mem_range_self q a
  have hRinf' : Module.finrank K ↥(R ⊓ q.range) = Module.finrank K ↥R := by
    apply le_antisymm hRinf
    exact Submodule.finrank_mono (le_inf le_rfl hRrange)
  omega

/-- Two linear maps with the same range and kernel, whose compression to `W` is the same and whose
range meets `ker q` trivially, are equal. -/
lemma eq_of_range_ker_eq {K : Type*} [Field K] {C N N' : Type*} [AddCommGroup C] [Module K C]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (W W₂ : Submodule K C) (hWW : W ≤ W₂) (q : N →ₗ[K] N')
    (X Y : ↥W₂ →ₗ[K] N) (Z : ↥W →ₗ[K] N')
    (hXsup : W ⊔ Submodule.map W₂.subtype X.ker = W₂)
    (hker : Y.ker = X.ker) (hrange : Y.range = X.range)
    (hdisjX : X.range ⊓ q.ker = ⊥)
    (hcompX : ∀ w, q (X (Submodule.inclusion hWW w)) = Z w)
    (hcompY : ∀ w, q (Y (Submodule.inclusion hWW w)) = Z w) :
    X = Y := by
  ext x
  obtain ⟨w, k, hwk⟩ := exists_inclusion_add_of_mem_sup W W₂ hWW X.ker hXsup x
  have hXx : X x = X (Submodule.inclusion hWW w) := by
    rw [hwk, map_add, LinearMap.mem_ker.mp k.2, add_zero]
  have hYx : Y x = Y (Submodule.inclusion hWW w) := by
    rw [hwk, map_add]
    have hkY : ((k : ↥W₂)) ∈ Y.ker := by rw [hker]; exact k.2
    rw [LinearMap.mem_ker.mp hkY, add_zero]
  have hincl : X (Submodule.inclusion hWW w) = Y (Submodule.inclusion hWW w) := by
    have hmemX : X (Submodule.inclusion hWW w) ∈ X.range := LinearMap.mem_range_self _ _
    have hmemY : Y (Submodule.inclusion hWW w) ∈ X.range := by
      rw [← hrange]; exact LinearMap.mem_range_self _ _
    have hdiff : X (Submodule.inclusion hWW w) - Y (Submodule.inclusion hWW w) ∈ X.range ⊓ q.ker := by
      refine ⟨Submodule.sub_mem _ hmemX hmemY, ?_⟩
      change X (Submodule.inclusion hWW w) - Y (Submodule.inclusion hWW w) ∈ q.ker
      rw [LinearMap.mem_ker, map_sub, hcompX w, hcompY w, sub_self]
    rw [hdisjX, Submodule.mem_bot] at hdiff
    exact sub_eq_zero.mp hdiff
  rw [hXx, hYx, hincl]

/-- The image of `ker X` in `W₂`, intersected with `W`, is the image of `ker Z` in `W`. -/
lemma map_subtype_ker_inf_eq {K : Type*} [Field K] {C N N' : Type*} [AddCommGroup C]
    [Module K C] [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (W W₂ : Submodule K C) (hWW : W ≤ W₂) (q : N →ₗ[K] N') (Z : ↥W →ₗ[K] N')
    (X : ↥W₂ →ₗ[K] N)
    (hdisjX : X.range ⊓ q.ker = ⊥)
    (hcompX : ∀ w, q (X (Submodule.inclusion hWW w)) = Z w) :
    Submodule.map W₂.subtype X.ker ⊓ W = Submodule.map W.subtype Z.ker := by
  apply le_antisymm
  · intro t ht
    rw [Submodule.mem_inf] at ht
    obtain ⟨htU, htW⟩ := ht
    rw [Submodule.mem_map] at htU ⊢
    obtain ⟨k, hk, hkt⟩ := htU
    refine ⟨⟨t, htW⟩, ?_, rfl⟩
    rw [LinearMap.mem_ker]
    have hz : Z ⟨t, htW⟩ = q (X (Submodule.inclusion hWW ⟨t, htW⟩)) := (hcompX ⟨t, htW⟩).symm
    rw [hz]
    have hink : Submodule.inclusion hWW ⟨t, htW⟩ = k := by
      apply Subtype.ext
      show t = (k : C)
      rw [← hkt]; rfl
    rw [hink, LinearMap.mem_ker.mp hk, map_zero]
  · intro t ht
    rw [Submodule.mem_map] at ht
    obtain ⟨w, hw, hwt⟩ := ht
    rw [Submodule.mem_inf, Submodule.mem_map]
    refine ⟨⟨Submodule.inclusion hWW w, ?_, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      have hmem : X (Submodule.inclusion hWW w) ∈ X.range ⊓ q.ker := by
        refine ⟨LinearMap.mem_range_self _ _, ?_⟩
        change q (X (Submodule.inclusion hWW w)) ∈ (⊥ : Submodule K N')
        rw [hcompX w, Submodule.mem_bot, LinearMap.mem_ker.mp hw]
      rw [hdisjX, Submodule.mem_bot] at hmem
      exact hmem
    · show ((w : C)) = t
      rw [← hwt]; rfl
    · rw [← hwt]; exact w.2


/-- **Counting the linear maps with a prescribed compression, a range avoiding a fixed subspace and
a kernel complementing a fixed subspace.**  Let `V₂ ≤ V₀` be subspaces of `B` and `W ≤ W₂` subspaces
of `C` over a finite field `K`, and let `Z : ↥W →ₗ[K] (B ⧸ V₀)`.  Then the number of
`X : ↥W₂ →ₗ[K] (B ⧸ V₂)` whose compression to `W` is `Z`, whose range meets `V₀/V₂` trivially and
whose kernel complements `W` in `W₂` is at most
`|K| ^ ((finrank V₀ - finrank V₂ + (finrank W₂ - finrank W)) * finrank (range Z))`.

Proof sketch: every such `X` has `rank X = finrank (range Z) =: k` (because `range X` is a
complement of `V₀/V₂` inside the preimage of `range Z` in `B ⧸ V₂`: its image under `B ⧸ V₂ → B ⧸ V₀`
is `range Z`, and it meets `V₀/V₂` trivially).  Moreover `X` is *determined* by the pair
`(range X, ker X)`: on `W` the compression `Z` and the directness of `range X + V₀/V₂` pin down `X`
uniquely, and `W ⊔ ker X = W₂` determines the rest.  Hence it suffices to count the pairs:
`range X` ranges over the complements of `V₀/V₂` inside the preimage of `range Z` (at most
`|K| ^ (k * (finrank V₀ - finrank V₂))` of them, by `card_complements_between`), and the image of
`ker X` in `W₂` ranges over the subspaces `U` with `(ker Z).map W.subtype ≤ U ≤ W₂`,
`U ⊓ W = (ker Z).map W.subtype`, `U ⊔ W = W₂` (at most `|K| ^ (k * (finrank W₂ - finrank W))` of
them, again by `card_complements_between`, using `ker Z = W ⊓ (image of ker X)` and
`finrank W - finrank (ker Z) = k`). -/
theorem card_hom_compress_le_pow {K : Type*} [Field K] [Fintype K] {B C : Type*}
    [AddCommGroup B] [Module K B] [Finite B] [AddCommGroup C] [Module K C] [Finite C]
    (V₂ V₀ : Submodule K B) (W W₂ : Submodule K C) (hVV : V₂ ≤ V₀) (hWW : W ≤ W₂)
    (Z : ↥W →ₗ[K] (B ⧸ V₀)) :
    Nat.card {X : ↥W₂ →ₗ[K] (B ⧸ V₂) //
        (Submodule.map (Submodule.mkQ V₂) V₀) ⊓ LinearMap.range X = ⊥ ∧
        W ⊔ Submodule.map W₂.subtype (LinearMap.ker X) = W₂ ∧
        (∀ w : ↥W, (Submodule.mapQ V₂ V₀ (LinearMap.id) (by simpa using hVV))
            (X (Submodule.inclusion hWW w)) = Z w)}
      ≤ Nat.card K ^ ((Module.finrank K V₀ - Module.finrank K V₂ +
          (Module.finrank K W₂ - Module.finrank K W)) *
          Module.finrank K (LinearMap.range Z)) := by
  classical
  letI : Finite (B ⧸ V₂) := Finite.of_surjective (Submodule.mkQ V₂) (Submodule.mkQ_surjective V₂)
  letI : Finite (B ⧸ V₀) := Finite.of_surjective (Submodule.mkQ V₀) (Submodule.mkQ_surjective V₀)
  let q : (B ⧸ V₂) →ₗ[K] (B ⧸ V₀) := Submodule.mapQ V₂ V₀ (LinearMap.id) (by simpa using hVV)
  let S : Submodule K (B ⧸ V₂) := Submodule.map (Submodule.mkQ V₂) V₀
  let P : Submodule K (B ⧸ V₂) := Submodule.comap q (LinearMap.range Z)
  let K₀ : Submodule K C := Submodule.map W.subtype (LinearMap.ker Z)
  have hqdef : q = Submodule.mapQ V₂ V₀ (LinearMap.id) (by simpa using hVV) := rfl
  have hSdef : S = Submodule.map (Submodule.mkQ V₂) V₀ := rfl
  have hPdef : P = Submodule.comap q (LinearMap.range Z) := rfl
  have hK0def : K₀ = Submodule.map W.subtype (LinearMap.ker Z) := rfl
  have hkerq : q.ker = S := by
    rw [hqdef, Submodule.ker_mapQ, hSdef]
    simp
  have hqrange : q.range = ⊤ := by
    rw [hqdef, Submodule.range_mapQ]
    simp
  have hSP : S ≤ P := by
    rw [← hkerq, hPdef]
    intro x hx
    rw [Submodule.mem_comap]
    rw [LinearMap.mem_ker] at hx
    rw [hx]
    exact (LinearMap.range Z).zero_mem
  have hK0W : K₀ ≤ W := by
    rw [hK0def]
    exact Submodule.map_subtype_le W (LinearMap.ker Z)
  have hrange_mem : ∀ (X : ↥W₂ →ₗ[K] (B ⧸ V₂)),
      S ⊓ X.range = ⊥ → W ⊔ Submodule.map W₂.subtype X.ker = W₂ →
      (∀ w : ↥W, q (X (Submodule.inclusion hWW w)) = Z w) →
      (X.range ≤ P ∧ X.range ⊓ S = ⊥ ∧ X.range ⊔ S = P) := by
    intro X h1 h2 h3
    have hmap : Submodule.map q X.range = LinearMap.range Z :=
      map_range_eq_of_comp_inclusion W W₂ hWW X q Z h2 h3
    have hdisj : X.range ⊓ q.ker = ⊥ := by rw [hkerq, inf_comm]; exact h1
    have hmain := finrank_eq_and_sup_ker_eq_comap q X.range (LinearMap.range Z) hmap hdisj
    refine ⟨?_, ?_, ?_⟩
    · rw [hPdef, ← Submodule.map_le_iff_le_comap, hmap]
    · rw [inf_comm]; exact h1
    · rw [← hkerq, hPdef]; exact hmain.2
  have hker_mem : ∀ (X : ↥W₂ →ₗ[K] (B ⧸ V₂)),
      S ⊓ X.range = ⊥ → W ⊔ Submodule.map W₂.subtype X.ker = W₂ →
      (∀ w : ↥W, q (X (Submodule.inclusion hWW w)) = Z w) →
      (K₀ ≤ Submodule.map W₂.subtype X.ker ∧ Submodule.map W₂.subtype X.ker ≤ W₂ ∧
        Submodule.map W₂.subtype X.ker ⊓ W = K₀ ∧ Submodule.map W₂.subtype X.ker ⊔ W = W₂) := by
    intro X h1 h2 h3
    have hdisj : X.range ⊓ q.ker = ⊥ := by rw [hkerq, inf_comm]; exact h1
    have hinf : Submodule.map W₂.subtype X.ker ⊓ W = K₀ := by
      rw [hK0def]
      exact map_subtype_ker_inf_eq W W₂ hWW q Z X hdisj h3
    refine ⟨?_, Submodule.map_subtype_le W₂ X.ker, hinf, ?_⟩
    · rw [← hinf]; exact inf_le_left
    · rw [sup_comm]; exact h2
  have hle : Nat.card {X : ↥W₂ →ₗ[K] (B ⧸ V₂) //
        S ⊓ X.range = ⊥ ∧ W ⊔ Submodule.map W₂.subtype X.ker = W₂ ∧
        (∀ w : ↥W, q (X (Submodule.inclusion hWW w)) = Z w)}
      ≤ Nat.card ({A : Submodule K (B ⧸ V₂) // A ≤ P ∧ A ⊓ S = ⊥ ∧ A ⊔ S = P} ×
          {U : Submodule K C // K₀ ≤ U ∧ U ≤ W₂ ∧ U ⊓ W = K₀ ∧ U ⊔ W = W₂}) := by
    apply Nat.card_le_card_of_injective
      (fun X => (⟨X.1.range, hrange_mem X.1 X.2.1 X.2.2.1 X.2.2.2⟩,
                 ⟨Submodule.map W₂.subtype X.1.ker, hker_mem X.1 X.2.1 X.2.2.1 X.2.2.2⟩))
    intro X Y hXY
    have hrange : Y.1.range = X.1.range := by
      have h := congrArg (fun p => (p.1 : Submodule K (B ⧸ V₂))) hXY
      exact h.symm
    have hkermap : Submodule.map W₂.subtype Y.1.ker = Submodule.map W₂.subtype X.1.ker := by
      have h := congrArg (fun p => (p.2 : Submodule K C)) hXY
      exact h.symm
    have hker : Y.1.ker = X.1.ker :=
      Submodule.map_injective_of_injective W₂.subtype_injective hkermap
    have hdisjX : X.1.range ⊓ q.ker = ⊥ := by rw [hkerq, inf_comm]; exact X.2.1
    apply Subtype.ext
    exact eq_of_range_ker_eq W W₂ hWW q X.1 Y.1 Z X.2.2.1 hker hrange hdisjX X.2.2.2 Y.2.2.2
  have hfinS : Module.finrank K ↥S = Module.finrank K V₀ - Module.finrank K V₂ := by
    have h := Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le (K := K) (V := B) V₂ V₀ hVV
    rw [hSdef]
    exact h
  have hfinP : Module.finrank K ↥P - Module.finrank K ↥S = Module.finrank K (LinearMap.range Z) := by
    have hcomap := Commons.LinearAlgebra.LinearMap.finrank_comap_eq q (LinearMap.range Z)
    rw [hqrange, inf_top_eq, hkerq] at hcomap
    have hcomap' : Module.finrank K ↥P = Module.finrank K ↥S + Module.finrank K (LinearMap.range Z) :=
      hcomap
    have hle' : Module.finrank K ↥S ≤ Module.finrank K ↥P := Submodule.finrank_mono hSP
    omega
  have hfinK0 : Module.finrank K ↥K₀ = Module.finrank K ↥(LinearMap.ker Z) := by
    rw [hK0def]
    exact Submodule.finrank_map_subtype_eq W (LinearMap.ker Z)
  have hfinW : Module.finrank K ↥W = Module.finrank K ↥(LinearMap.ker Z) +
      Module.finrank K (LinearMap.range Z) := by
    have h := LinearMap.finrank_range_add_finrank_ker Z
    omega
  have hfinal : Nat.card ({A : Submodule K (B ⧸ V₂) // A ≤ P ∧ A ⊓ S = ⊥ ∧ A ⊔ S = P} ×
        {U : Submodule K C // K₀ ≤ U ∧ U ≤ W₂ ∧ U ⊓ W = K₀ ∧ U ⊔ W = W₂})
      = Nat.card K ^ ((Module.finrank K V₀ - Module.finrank K V₂ +
          (Module.finrank K W₂ - Module.finrank K W)) * Module.finrank K (LinearMap.range Z)) := by
    rw [Nat.card_prod, Commons.LinearAlgebra.Submodule.card_complements S P hSP,
        Commons.LinearAlgebra.Submodule.card_complements_between K₀ W W₂ hK0W hWW, ← pow_add]
    congr 1
    rw [hfinP, hfinK0, hfinW, hfinS]
    have hsub : Module.finrank K ↥(LinearMap.ker Z) + Module.finrank K (LinearMap.range Z) -
        Module.finrank K ↥(LinearMap.ker Z) = Module.finrank K (LinearMap.range Z) := by omega
    rw [hsub]
    ring
  exact hle.trans (le_of_eq hfinal)

end

end Commons.LinearAlgebra.LinearMap
