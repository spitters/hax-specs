//! NIST CAVP GCMVS decrypt-side Known-Answer Tests for AES-128/256-GCM.
//!
//! Vectors are copied verbatim from `gcmDecrypt128.rsp` and
//! `gcmDecrypt256.rsp` (CAVS 14.0, generated 2012-08-31), section
//! `[IVlen = 96] [PTlen = 128] [AADlen = 128] [Taglen = 128]`, Count 0 to 6.
//! A vector marked `FAIL` in the response file carries a tag that must be
//! rejected; the others carry the expected plaintext.

use aesgcm_hax::realgcm::{gcm_decrypt_var, AesVariant};
use aesgcm_hax::types::{GcmNonce, GcmTag};

fn hex(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd hex length");
    let b = s.as_bytes();
    (0..b.len() / 2)
        .map(|i| {
            let hi = (b[2 * i] as char).to_digit(16).expect("hex") as u8;
            let lo = (b[2 * i + 1] as char).to_digit(16).expect("hex") as u8;
            (hi << 4) | lo
        })
        .collect()
}

/// One CAVP decrypt vector: `pt` is `None` for a `FAIL` line.
struct Vector {
    key: &'static str,
    iv: &'static str,
    ct: &'static str,
    aad: &'static str,
    tag: &'static str,
    pt: Option<&'static str>,
}

fn check(variant: AesVariant, v: &Vector) {
    let mut key = [0u8; 32];
    let kb = hex(v.key);
    key[..kb.len()].copy_from_slice(&kb);
    let mut nonce: GcmNonce = [0u8; 12];
    nonce.copy_from_slice(&hex(v.iv));
    let mut tag: GcmTag = [0u8; 16];
    tag.copy_from_slice(&hex(v.tag));
    let ct = hex(v.ct);
    let aad = hex(v.aad);

    let mut pt = vec![0xAAu8; ct.len()];
    let ok = gcm_decrypt_var(variant, &key, &nonce, &aad, &ct, &tag, &mut pt);
    match v.pt {
        Some(expected) => {
            assert!(ok, "tag rejected on a PASS vector");
            assert_eq!(pt, hex(expected), "plaintext mismatch vs NIST vector");
        }
        None => {
            assert!(!ok, "tag accepted on a FAIL vector");
            assert!(pt.iter().all(|&b| b == 0xAA), "plaintext written on a FAIL vector");
        }
    }
}

// gcmDecrypt128.rsp [Keylen = 128][IVlen = 96][PTlen = 128][AADlen = 128][Taglen = 128]
const AES128: [Vector; 7] = [
    // Count = 0
    Vector {
        key: "816e39070410cf2184904da03ea5075a",
        iv: "32c367a3362613b27fc3e67e",
        ct: "552ebe012e7bcf90fcef712f8344e8f1",
        aad: "f2a30728ed874ee02983c294435d3c16",
        tag: "ecaae9fc68276a45ab0ca3cb9dd9539f",
        pt: Some("ecafe96c67a1646744f1c891f5e69427"),
    },
    // Count = 1 (FAIL)
    Vector {
        key: "867fc5d5476d5008f0703d81e3622255",
        iv: "22945529dff947c3c9264df7",
        ct: "1c785025e5a2678e4b29b29276e395bb",
        aad: "261a9efd4f32bc3d07c115b4edcf8adf",
        tag: "87fdf1261846164a950c37a3f2eea17d",
        pt: None,
    },
    // Count = 2
    Vector {
        key: "3d17f97bf1dae4268b6610dc90c70b28",
        iv: "ebcd88fc18d4c99d28524d41",
        ct: "0128a239bb43c12885f9591386ecac0f",
        aad: "681a4feac147ee2d25e9191aaa4c8830",
        tag: "144def0210af9348f07afe27e65bdc7e",
        pt: Some("ec18a057c22d12373b5efe4d177eb068"),
    },
    // Count = 3 (FAIL)
    Vector {
        key: "5c32091e288d4780fcaff52a69c1234e",
        iv: "bedb360b22847fc2ff60ab78",
        ct: "60c883306c91a0e6e98f8d7bf7ee9fd9",
        aad: "dc7c3a89a00b688af2bd372530bfed0b",
        tag: "ffb93af9106e95e9a65ef147765970da",
        pt: None,
    },
    // Count = 4 (FAIL)
    Vector {
        key: "75fb7f243336b78979988c08f39c44ab",
        iv: "69fed95864cad27f83503f8d",
        ct: "7bb1d878239966163a3db5712f57b096",
        aad: "b4783565715e8cdb46f8a2bb72030ce2",
        tag: "bfee0dda5e1afde5c7b0928774f80d21",
        pt: None,
    },
    // Count = 5
    Vector {
        key: "7a3d71615ec0e6ee2257f33d06611b89",
        iv: "1ccf177092a1518be9f6612f",
        ct: "d0bb72968ff7fdbd3499d6e7a34ec043",
        aad: "0753ecc820e7ed3b6ce6b60dde776fdf",
        tag: "3a7c708e0e6e74a654987a257ab96461",
        pt: Some("9c0e1b4ea43af8b1d4d173b31424fa40"),
    },
    // Count = 6
    Vector {
        key: "bf283c584efcc4778bc6091804b2b66d",
        iv: "1fad1f81b45de44392497629",
        ct: "51f94491184b13f46defe609642adc16",
        aad: "791856131d5d4ed0e7b205b8b2ff4012",
        tag: "f2e8b0bc4e1bdd9d2604c0607c4f7fc7",
        pt: Some("c40fee049bac9b688601506d63450869"),
    },
];

// gcmDecrypt256.rsp [Keylen = 256][IVlen = 96][PTlen = 128][AADlen = 128][Taglen = 128]
const AES256: [Vector; 7] = [
    // Count = 0
    Vector {
        key: "54e352ea1d84bfe64a1011096111fbe7668ad2203d902a01458c3bbd85bfce14",
        iv: "df7c3bca00396d0c018495d9",
        ct: "426e0efc693b7be1f3018db7ddbb7e4d",
        aad: "7e968d71b50c1f11fd001f3fef49d045",
        tag: "ee8257795be6a1164d7e1d2d6cac77a7",
        pt: Some("85fc3dfad9b5a8d3258e4fc44571bd3b"),
    },
    // Count = 1
    Vector {
        key: "82f0d1ddc58123f805541f55a7eab43f56ddfefc06c73d57709df3d5a4aabfb3",
        iv: "0c9d74af29ed4406c77a8e4b",
        ct: "c61155d41495e9fc76060fe7f8c926a2",
        aad: "34325620a392739beeee6c370967d539",
        tag: "66d8c881d66370504d2bf00cdb06259e",
        pt: Some("3fe7811a8224a1881da34a27e03da86a"),
    },
    // Count = 2 (FAIL)
    Vector {
        key: "9a0343f850a6427120f764789ffec6d237447b898fbf51d2182f065d3861497d",
        iv: "3deef6f453dd70d92143adcd",
        ct: "e93165935ac18e3a2845d15fe31a9286",
        aad: "dbb8226a624520863db6897017b2a4f8",
        tag: "f5fc50d18766bc3d9e16dd136d45816b",
        pt: None,
    },
    // Count = 3
    Vector {
        key: "562a865ddc042577284b34b6cd267aa3e9adedf6b8a9e2490d5519eaea3daccc",
        iv: "f20e5db286f3ee11835a5103",
        ct: "ae62b52018c253be2463ff235cd3ff1d",
        aad: "c638e57814cd44f8af9730208f5464d5",
        tag: "6e481954d30c503ce6d448fda4116578",
        pt: Some("7e59320cc09d1ccfb49f7c90e81326dc"),
    },
    // Count = 4 (FAIL)
    Vector {
        key: "2a765ceac97265c15209eea90bea85cd9586b972160502ff592a306dc017e6b9",
        iv: "62c545d9d4e3c7acb66b4bf1",
        ct: "ae0594a7b66d3a958e4e6212d3288f91",
        aad: "7d12474e23dc233bc6312d4d5b2deee4",
        tag: "ec9aa846d185cc0f43d392240cd6e2c4",
        pt: None,
    },
    // Count = 5
    Vector {
        key: "b919ab155fc93ad5f3bac0e9706999031a3175356b070bd45fa6dbe7099126d0",
        iv: "e65d8f9f6b67d5b333191044",
        ct: "3da7bfdbe0fc98a1b657f70b2c046f46",
        aad: "b04f3b04764aa3208165e8374faea266",
        tag: "d9bfbcb1a1027b0d5dbe9e0accf587b5",
        pt: Some("0c5b45bf8168b2cd8069702624c68dc5"),
    },
    // Count = 6 (FAIL)
    Vector {
        key: "2b44f83492c05b784b6d9405c64a0530eb9ac7fcd6d5d1f0e3d4ab015a07398b",
        iv: "88c16315108517124ba3b280",
        ct: "a0df8e1083853d740e80dd77e3a78d10",
        aad: "af6406f8222a287ef1086a264929dfc5",
        tag: "08d0184cb2cbec32ebbebb30fb253e74",
        pt: None,
    },
];

#[test]
fn cavp_gcm_decrypt_128() {
    for v in AES128.iter() {
        check(AesVariant::Aes128, v);
    }
}

#[test]
fn cavp_gcm_decrypt_256() {
    for v in AES256.iter() {
        check(AesVariant::Aes256, v);
    }
}
